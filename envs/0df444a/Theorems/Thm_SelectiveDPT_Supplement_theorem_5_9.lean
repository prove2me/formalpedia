-- Prove2me | Theorems.Thm_SelectiveDPT_Supplement_theorem_5_9
-- name    : SelectiveDPT.Supplement.theorem_5_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T00:38:28.79519+00:00
-- url     : https://prove2.me/theorems/613edb96-c28a-496a-844a-6833c791feb5
-- title:
--   Theorem 5.9 (corrected: $|Y|\ge2$) — multiplicative adversary with $\eta = 1/|Y|$ gives a strong list-decoding DPT
-- statement:
--   Let $\lambda > 1$. There is $k_0 = k_0(\lambda) \ge 1$ such that the following holds for every alphabet size $d$, every $n$, every finite set $Y$ with $|Y| \ge 2$, every domain $D \subseteq X^n$, every function $f : D \to Y$ and every distribution $\mathcal D$ on $D$. Suppose $f$ satisfies Proposition 2.12 for $\mathcal D$ with an adversary matrix $\Gamma$, the given $\lambda \in (1, \|\Gamma\|]$ and $\eta = 1/|Y|$, and let the error probability satisfy
--   $$\frac12 - \frac1{|Y|} - \sqrt{\frac2{|Y|}} \;\le\; \varepsilon \;<\; 1 - \frac1{|Y|}.$$
--   Then there is $\kappa \in (0, 1)$ such that for all integers $k \ge k_0$ and all $m$,
--   $$Q^{\mathcal D^{\otimes m}}_{1-\kappa^k}\big(f^{L(k,m)}\big) \;\ge\; \frac k8\, \mathrm{MADV}^{\mathcal D}_{\varepsilon,\lambda,1/|Y|}(f).$$
--
--   The left side is the number of queries needed to output, with probability at least $\kappa^k$ over $m$ independent inputs from $\mathcal D$, a list of at most $|Y|^{m-k}$ answer vectors containing $f^{\otimes m}(x)$. So every function with a multiplicative adversary bound at the threshold $\eta = 1/|Y|$ has a strong list-decoding direct product theorem.
--
--   Differences from the source:
--   - correction: f : D → Y (Y any finite set) → |Y| ≥ 2; reason: the proof uses |Y| ≥ 2 (p.46); at |Y| = 1 every one-element list is always correct with 0 queries, so the left side is 0, while for ε = −1/10 (inside the printed range) a witness with rate c(Γ) > 1 (e.g. D = {0,1}, n = 1, d = 2, uniform μ, Γ = I + |−⟩⟨−|) makes MADV positive
--   - reading: There is an k₀ = k₀(λ) ≥ 1 and a κ < 1 such that for any integers k ≥ k₀ and m → k₀ ≥ 1 chosen after λ only; κ chosen after d, n, Y, D, f, μ, Γ and ε, before k and m; reason: the notation k₀(λ) says k₀ depends on λ alone; κ is stated without such a restriction
--   - generalization: κ < 1 → 0 < κ < 1; reason: the proof's κ = κ(k₀) is positive; a positive κ is needed for the claim to be nonvacuous at even k (as in the base Theorem 4.7)
--   - encoding: f satisfying Proposition 2.12 for D with adversary matrix Γ, λ ∈ (1, ‖Γ‖], η = 1/|Y| → IsMultAdvWitness μ D f Γ λ (1/|Y|) (base), for a distribution μ with IsDistOn μ D; reason: the base mission's encoding of the witness conditions of Propositions 2.12 and 2.14, which include λ ∈ (1, ‖Γ‖]
--   - generalization: L ∈ (Y^m choose |Y|^{m−k}) (Definition 5.1, lists of exactly |Y|^{m−k} vectors) → lists L ⊆ Y^m with |L|·|Y|^k ≤ |Y|^m (listRel); reason: every list of the exact size qualifies, so the Lean statement covers the source's; the size 'at most |Y|^{m−k}' is the one of the introduction (p.6) and of the proofs (p.46)
--   - encoding: inputs x ∈ X^n with |X| = d, a T-query algorithm measuring its work register and post-processing the result → X = ZMod d, inputs Fin n → ZMod d with a Finset domain D, QAlgorithms.QueryAlg with workspace Fin b for any b, a full computational-basis measurement followed by an output map, query complexity in ℕ∞ (⊤ if no algorithm exists) compared in [0, ∞]; reason: relabelling X as Z_d is the paper's own convention (p.9); only the workspace dimension matters; measuring a designated output register is a special output map
-- source:
--   Beame–Kornerup–Whitmeyer, Strong Selective and List-Decoding Direct Product Theorems for Quantum Query Complexity, arXiv:2609.26678, Theorem 5.9, p.45

import Mathlib
import Definitions.Def_SelectiveDPT_Qdist
import Definitions.Def_SelectiveDPT_madv
import Definitions.Def_SelectiveDPT_prodDomain
import Definitions.Def_SelectiveDPT_prodDist
import Definitions.Def_SelectiveDPT_Supplement_listRel

open scoped ENNReal

universe u

namespace SelectiveDPT.Supplement

/-- Theorem 5.9 of arXiv:2609.26678 (Beame–Kornerup–Whitmeyer), p.45: let `f : D → Y` be a function
satisfying Proposition 2.12 for distribution `D` over `D ⊆ X^n` with adversary matrix `Γ`,
`λ ∈ (1, ‖Γ‖]`, `η = 1/|Y|`, and with error probability
`1/2 − 1/|Y| − √(2/|Y|) ≤ ε < 1 − 1/|Y|`. There is a `k₀ = k₀(λ) ≥ 1` and a `κ < 1` such that for
any integers `k ≥ k₀` and `m`: `Q^{D^{⊗m}}_{1−κ^k}(f^{L(k,m)}) ≥ (k/8) MADV^D_{ε,λ,1/|Y|}(f)`.

**Formalization Note.** `k₀` is chosen after `λ` only, before `d`, `n`, `Y`, `D`, `f`, `μ`, `Γ`,
`ε`; `κ` after all of these and before `k`, `m`. `0 < κ` is added (it holds for the proof's `κ`;
without it `κ ≤ 0` would make the claim vacuous for even `k`). The witness condition is the base
`IsMultAdvWitness` (which contains `λ ∈ (1, ‖Γ‖]`). The left side is the distributional
complexity (base `Qdist`) of the list-decoding relation (`listRel`) of the graph of `f` under the
product distribution `μ^m` on `D^m`; `m` is arbitrary (for `m < k` no list qualifies and the
complexity is `⊤`). **Correction:** `|Y| ≥ 2`, which the proof uses ("since `|Y| ≥ 2`", p.46). At
`|Y| = 1` the claim is false: every one-element list is always correct with `0` queries, so the
left side is `0`, while for `ε = −1/10` (inside the printed range) a witness with rate `c(Γ) > 1`
gives `MADV > 0`. -/
theorem theorem_5_9 (lam : ℝ) (hlam : 1 < lam) :
    ∃ k₀ : ℕ, 1 ≤ k₀ ∧
      ∀ (d n : ℕ) [NeZero d] (Y : Type u) [Fintype Y] [DecidableEq Y], 2 ≤ Fintype.card Y →
      ∀ (D : Finset (Fin n → ZMod d)) (f : (Fin n → ZMod d) → Y) (μ : (Fin n → ZMod d) → ℝ),
        IsDistOn μ D →
      ∀ Γ : Matrix D D ℂ,
        IsMultAdvWitness μ D (fun x y => f x = y) Γ lam (1 / (Fintype.card Y : ℝ)) →
      ∀ ε : ℝ, 1 / 2 - 1 / (Fintype.card Y : ℝ) - Real.sqrt (2 / (Fintype.card Y : ℝ)) ≤ ε →
        ε < 1 - 1 / (Fintype.card Y : ℝ) →
      ∃ κ : ℝ, 0 < κ ∧ κ < 1 ∧ ∀ k m : ℕ, k₀ ≤ k →
        ENNReal.ofReal ((k : ℝ) / 8) *
            madv μ D (fun x y => f x = y) ε lam (1 / (Fintype.card Y : ℝ)) ≤
          (Qdist (prodDomain D m) (prodDist μ m) (listRel k m (fun x y => f x = y))
            (1 - κ ^ k) : ℝ≥0∞) := by sorry

end SelectiveDPT.Supplement
