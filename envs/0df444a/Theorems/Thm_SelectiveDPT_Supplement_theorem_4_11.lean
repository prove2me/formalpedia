-- Prove2me | Theorems.Thm_SelectiveDPT_Supplement_theorem_4_11
-- name    : SelectiveDPT.Supplement.theorem_4_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T00:34:28.960428+00:00
-- url     : https://prove2.me/theorems/e31a41c4-f857-456d-b4f7-f789c8fb727b
-- title:
--   Theorem 4.11 (corrected: distinct copies; $\delta\le1/2$ in the entropy bound) — $(1-\delta)$-correct $\Rightarrow$ $f^{(\lceil(1-\delta)k\rceil,m)}$ w.p. $q_k/\binom{k}{k'}$
-- statement:
--   Let $f \subseteq D \times Y$ be a relation, $1 \le k \le m$, $0 \le \delta \le 1$ and $q_k \ge 0$. Suppose an algorithm makes at most $T$ queries and, on every input $x \in D^m$, is $(1-\delta)$-correct for $f^{(k,m)}$ with probability at least $q_k$: it outputs at most $k$ pairs (copy, answer) with distinct copies, at least $(1-\delta)k$ of them correct. Let $k' = \lceil (1-\delta)k \rceil$. Then there is an algorithm making at most $T$ queries that computes $f^{(k',m)}$ on every input $x \in D^m$ with probability at least
--   $$\frac{q_k}{\binom{k}{k'}},$$
--   and, when $\delta \le 1/2$,
--   $$\frac{q_k}{\binom{k}{k'}} \;\ge\; q_k \cdot 2^{-H_2(\delta)k},$$
--   where $H_2$ is the binary entropy function.
--
--   So any strong selective direct product theorem yields a threshold version in which a $\delta$ fraction of the $k$ answers may be wrong (Corollary 4.12).
--
--   Differences from the source:
--   - correction: a set of pairs (i_1, y_1), …, (i_ℓ, y_ℓ) (Definition 4.10) → the copy indices i_j are pairwise distinct (approxSelRel); reason: without it the theorem is false: m = 1, k = 2, δ = 0 and an algorithm that writes the same correct pair twice is (1−δ)-correct with q = 1, while f^(2,1) has no correct output; the proof orders the indices i_1 < ⋯ < i_k
--   - correction: q_k/(k choose k′) ≥ q_k · 2^{−H₂(δ)k} (every δ) → this inequality for δ ≤ 1/2 only; reason: the proof's step H₂((k−k′)/k) ≤ H₂(δ) needs δ ≤ 1/2; at k = 10, δ = 0.99, k′ = 1 and q_k > 0 it reads q_k/10 ≥ q_k · 2^{−10·H₂(0.99)} ≈ 0.57 q_k, false
--   - reading: δ, q_k, k, m unconstrained in the statement → 1 ≤ k ≤ m, 0 ≤ δ ≤ 1, q_k ≥ 0; reason: Definition 4.10 assumes 1 ≤ k ≤ m; δ is a fraction of the k answers; q_k is a probability
--   - generalization: for each x ∈ X^m → for each x ∈ D^m, for a relation on any domain D ⊆ X^n; reason: D = X^n is the printed case; the proof never uses that D is all of X^n
--   - encoding: an algorithm making at most T queries → a QueryAlg with exactly T queries in the hypothesis, one with some T′ ≤ T queries in the conclusion; reason: the hypothesis is stated for every T, so an algorithm with fewer queries is the case of a smaller T
--   - encoding: outputs (i_1, y_1), …, (i_ℓ, y_ℓ) with ℓ ≤ k → Fin k → Option (Fin m × Y), the some entries being the pairs; reason: an empty slot is an unused pair; same outputs
--   - encoding: inputs x ∈ X^n with |X| = d, a T-query algorithm measuring its work register and post-processing the result → X = ZMod d, inputs Fin n → ZMod d with a Finset domain D, QAlgorithms.QueryAlg with workspace Fin b for any b, a full computational-basis measurement followed by an output map, query complexity in ℕ∞ (⊤ if no algorithm exists) compared in [0, ∞]; reason: relabelling X as Z_d is the paper's own convention (p.9); only the workspace dimension matters; measuring a designated output register is a special output map
-- source:
--   Beame–Kornerup–Whitmeyer, Strong Selective and List-Decoding Direct Product Theorems for Quantum Query Complexity, arXiv:2609.26678, Theorem 4.11, pp.37–38; Definition 4.10, p.37

import Mathlib
import Definitions.Def_SelectiveDPT_Qrel
import Definitions.Def_SelectiveDPT_prodDomain
import Definitions.Def_SelectiveDPT_selRel
import Definitions.Def_SelectiveDPT_H2
import Definitions.Def_SelectiveDPT_Supplement_approxSelRel

namespace SelectiveDPT.Supplement

open QAlgorithms

/-- Theorem 4.11 of arXiv:2609.26678 (Beame–Kornerup–Whitmeyer), pp.37–38: let `f` be a relation.
Suppose that there is an algorithm that makes at most `T` queries and for each `x ∈ X^m` is
`(1 − δ)`-correct at computing `f^(k,m)` on `x` with probability at least `q_k`. Then there is an
algorithm making at most `T` queries that correctly computes `f^(k′,m)` for `k′ = ⌈(1 − δ)k⌉` on
each input `x ∈ X^m` with probability at least `q_k / (k choose k′) ≥ q_k · 2^{−H₂(δ)k}`.

**Formalization Note.** `1 ≤ k ≤ m` and `0 ≤ δ ≤ 1` (Definition 4.10); `q_k ≥ 0` is a probability.
`(1 − δ)`-correctness is `approxSelRel` (at most `k` pairs with distinct copies, at least `(1 − δ)k`
of them correct). The relation is on a general domain `D ⊆ X^n` and "each `x ∈ X^m`" is each
`x ∈ D^m` (`D = X^n` is the printed case). Both algorithms are base `QueryAlg`s with a full
measurement and a post-processing. **Correction:** the second inequality
`q_k/(k choose k′) ≥ q_k · 2^{−H₂(δ)k}` is claimed for `δ ≤ 1/2` only (the proof's step
`H₂((k − k′)/k) ≤ H₂(δ)` needs it; at `k = 10`, `δ = 0.99`, `k′ = 1` it reads
`1/10 ≥ 2^{−10·H₂(0.99)} ≈ 0.57`, false). -/
theorem theorem_4_11 {ι Y : Type*} [Fintype ι] [DecidableEq ι] {d : ℕ} [NeZero d]
    (D : Finset (ι → ZMod d)) (R : (ι → ZMod d) → Y → Prop) (k m : ℕ) (hk : 1 ≤ k)
    (hkm : k ≤ m) (δ : ℝ) (hδ₀ : 0 ≤ δ) (hδ₁ : δ ≤ 1) (q : ℝ) (hq : 0 ≤ q) (b T : ℕ)
    (A : QueryAlg (Fin m × ι) (ZMod d) (Fin b) T)
    (out : ((Fin m × ι) × ZMod d) × Fin b → (Fin k → Option (Fin m × Y)))
    (hA : ∀ x ∈ prodDomain D m, q ≤ successProb A out (approxSelRel k m δ R) x) :
    (∃ T' : ℕ, T' ≤ T ∧ ∃ (b' : ℕ) (A' : QueryAlg (Fin m × ι) (ZMod d) (Fin b') T')
      (out' : ((Fin m × ι) × ZMod d) × Fin b' → (Fin ⌈(1 - δ) * k⌉₊ → Fin m × Y)),
      ∀ x ∈ prodDomain D m,
        q / (k.choose ⌈(1 - δ) * k⌉₊ : ℝ) ≤ successProb A' out' (selRel ⌈(1 - δ) * k⌉₊ m R) x) ∧
    (δ ≤ 1 / 2 → q * (2 : ℝ) ^ (-(H2 δ * k)) ≤ q / (k.choose ⌈(1 - δ) * k⌉₊ : ℝ)) := by sorry

end SelectiveDPT.Supplement
