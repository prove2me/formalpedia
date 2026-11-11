-- Prove2me | Theorems.Thm_RandKSATSample_Main_lemma_3_7
-- name    : RandKSATSample.Main.lemma_3_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:00:03.951281+00:00
-- url     : https://prove2.me/theorems/4201c135-7ea5-4007-b02a-2101ba7ef459
-- title:
--   Lemma 3.7 — core feasibility: the core formula is satisfiable for every sign choice, Ω = ∏Ω_i ≠ ∅, I(B_i) ≤ 4 ln n/(1 − 25/(3k³)), c_i ≤ |B_i|/(k−4), and the rejection sampler's acceptance bound
-- statement:
--   Let $k\ge30$, assume the joint event of Lemmas 3.1 to 3.3 and $r\ge\lceil\log_2n\rceil$. Then:
--   1. the core formula (the core clauses) is satisfiable for every choice of literal signs;
--   2. every $\Omega_i$ (assignments of $B_i$ satisfying the core clauses meeting $B_i$) is nonempty, and an assignment of $V_{\mathrm{bad}}$ satisfies the core formula iff its restriction to every $B_i$ lies in $\Omega_i$, i.e. the feasible set is $\Omega=\prod_i\Omega_i\neq\emptyset$;
--   3. for every component, with $c_i$ the number of core clauses in $B_i$, $\theta=\frac{2^{-k+4}}{1-2^{-k+4}}$ and $\kappa=\theta\cdot\frac{2k^2}{\Delta(1-25/(3k^3))(k-4)}$:
--   $$I(B_i)\le\frac{4\ln n}{1-25/(3k^3)},\qquad c_i\le\frac{|B_i|}{k-4},\qquad \frac{|\Omega_i|}{2^{|B_i|}}\ge(1-2^{-k+4})^{c_i}\ge e^{-c_i\theta},\qquad e^{c_i\theta}\le n^{\kappa}.$$
--   The last two bounds are the content of the paper's cost bound $U_i\le\tilde O((|B_i|+kc_i+1)e^{c_i\theta})=\tilde O(\mathrm{poly}(k,\lambda)n^\kappa)$ for the rejection sampler that draws $|B_i|$ fair bits per candidate and checks at most $kc_i$ literal occurrences: its acceptance probability is $|\Omega_i|/2^{|B_i|}$, so its expected number of candidates is at most $e^{c_i\theta}\le n^\kappa$.
--
--   Differences from the source:
--   - reading: Assume the joint event of Lemmas 3.1 to 3.3 → hypotheses JointEvent Φ and k ≥ 30; reason: the joint event is that of Lemmas 3.1 and 3.3, which are stated for k ≥ 30, and the proof uses k ≥ 30 (p. 15, last display); without it the statement fails (k = 1, see INSIGHTS.yaml I1)
--   - reading: the expected cost U_i of the rejection sampler is at most Õ((|B_i| + kc_i + 1) exp(c_i 2^{−k+4}/(1 − 2^{−k+4}))) = Õ(poly(k, λ) n^κ) → |Ω_i|/2^{|B_i|} ≥ (1 − 2^{−k+4})^{c_i} ≥ exp(−c_i θ) and exp(c_i θ) ≤ n^κ; reason: the clause is about an unspecified sampler program; its mathematical content is the acceptance probability (geometric number of candidates, mean 2^{|B_i|}/|Ω_i|) and the bound by n^κ, as derived on p. 17; the per-candidate work (|B_i| fair bits, ≤ kc_i checks) is a property of the procedure, not of Φ
--   - encoding: Ω = ∏_{i=1}^s Ω_i, the feasible set of the core formula → σ ∈ Omega Φ ↔ ∀ B_i, restriction of σ to B_i ∈ Ω_i, plus every Ω_i nonempty; reason: an assignment of V_bad is a tuple of assignments of the disjoint B_i; the same set
--   - encoding: satisfiable with any choice of literal signs → ∀ signs sg : Fin m → Fin k → Bool, some assignment of V_bad makes, in each core clause, some literal (with its variable from Φ and its sign from sg) true; reason: V_bad and the core clauses depend only on the variables of the occurrences, so changing the signs is exactly this quantifier
-- source:
--   He, Li, Yang, Fast Almost-Uniform Sampling of Random k-SAT Solutions, arXiv:2610.10474 (version not printed; file sha256 563a4d84…), p. 16, Lemma 3.7

import Mathlib
import Definitions.Def_RandKSATSample_Main_Formula
import Definitions.Def_RandKSATSample_Main_Structure

set_option autoImplicit false

open Classical

namespace RandKSATSample.Main

/-- Lemma 3.7: on the joint event of Lemmas 3.1–3.3 (whose lemmas assume `k ≥ 30`) with
`r ≥ ⌈log₂ n⌉`, the core formula is satisfiable for every choice of literal signs; every `Ω_i` is
nonempty and the feasible set of the core formula is `Π_i Ω_i`; for every component `B_i`,
`I(B_i) ≤ 4 ln n/(1 − 25/(3k³))`, `c_i ≤ |B_i|/(k − 4)`, the rejection sampler's acceptance
probability `|Ω_i|/2^{|B_i|}` is at least `(1 − 2^{−k+4})^{c_i} ≥ exp(−c_i θ)` with
`θ = 2^{−k+4}/(1 − 2^{−k+4})`, and `exp(c_i θ) ≤ n^κ`. -/
theorem lemma_3_7 {n m k : ℕ} (hk : 30 ≤ k) (Φ : Formula n m k) (hJ : JointEvent Φ)
    (hr : ⌈Real.logb 2 n⌉₊ ≤ rpar n m k) :
    let θ : ℝ := (2 : ℝ) ^ ((4 : ℤ) - k) / (1 - (2 : ℝ) ^ ((4 : ℤ) - k))
    let κ : ℝ := θ * (2 * (k : ℝ) ^ 2 /
      (Delta n m k * (1 - 25 / (3 * (k : ℝ) ^ 3)) * ((k : ℝ) - 4)))
    (∀ sg : Fin m → Fin k → Bool, ∃ σ : PartAssign n (Vbad Φ), ∀ a : Fin m, IsCore Φ a →
      ∃ i : Fin k, ∃ h : (Φ a i).1 ∈ Vbad Φ, σ ⟨(Φ a i).1, h⟩ = sg a i) ∧
    (∀ Bi ∈ blocks Φ, (OmegaBlock Φ Bi).Nonempty) ∧
    (∀ σ : PartAssign n (Vbad Φ),
      σ ∈ Omega Φ ↔ ∀ Bi ∈ blocks Φ, restrictTo σ Bi ∈ OmegaBlock Φ Bi) ∧
    ∀ Bi ∈ blocks Φ,
      let c : ℕ := (Finset.univ.filter fun a : Fin m => IsCore Φ a ∧ vbl Φ a ⊆ Bi).card
      (incident Φ Bi : ℝ) ≤ 4 * Real.log n / (1 - 25 / (3 * (k : ℝ) ^ 3)) ∧
      (c : ℝ) ≤ (Bi.card : ℝ) / ((k : ℝ) - 4) ∧
      (1 - (2 : ℝ) ^ ((4 : ℤ) - k)) ^ c ≤ ((OmegaBlock Φ Bi).card : ℝ) / (2 : ℝ) ^ Bi.card ∧
      Real.exp (-(c * θ)) ≤ (1 - (2 : ℝ) ^ ((4 : ℤ) - k)) ^ c ∧
      Real.exp (c * θ) ≤ (n : ℝ) ^ κ := by sorry

end RandKSATSample.Main
