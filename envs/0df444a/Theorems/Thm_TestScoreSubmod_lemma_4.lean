-- Prove2me | Theorems.Thm_TestScoreSubmod_lemma_4
-- name    : TestScoreSubmod.lemma_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:49:31.158643+00:00
-- url     : https://prove2.me/theorems/594ac7b3-5990-4114-95e7-268349a940ba
-- title:
--   Lemma 4 (corrected: lower sketch on $|S|=k$, upper sketch on $0<|S|\le k$): replication scores are $(1-1/e,4)$-good
-- statement:
--   Let $0<k\le n=m+1$, let $g:\mathbb R_+^n\to\mathbb R_+$ be a measurable, symmetric, monotone submodular value function, and let $X_i\sim P_i$ be independent nonnegative performances whose $k$-fold replicas have integrable value.
--   Suppose moreover that $g$ has the extended diminishing returns property. Let $u(S)=\mathbb E[g(M_S(X))]$ and let $a_i$ be the replication test scores (7). Then
--
--   1. $\bigl(1-\frac1e\bigr)\min_{i\in S}a_i\le u(S)$ for every $S$ with $|S|=k$, and
--   2. $u(S)\le4\max_{i\in S}a_i$ for every nonempty $S$ with $|S|\le k$.
--
--   So the replication test scores are $(1-1/e,4)$-good, and hence good test scores: the sketch $(\min a,\max a)$ approximates $u$ within the constant ratio $4/(1-1/e)$.
--
--   Differences from the source:
--
--   - correction: (1 − 1/e) min_{i∈S} aᵢ ≤ u(S) for all S ⊆ N (Definition 3) → for every S with |S| = k; reason: false for other sizes: g = Σᵢ xᵢ, Xᵢ ≡ 1, k = 2, n ≥ 2, S = {1} gives 2(1 − 1/e) > 1 = u(S); min ∅ is undefined; Appendices C and D (p.35) prove it for |S| = k
--   - correction: u(S) ≤ 4 max_{i∈S} aᵢ for all S ⊆ N (Definition 3) → for every nonempty S with |S| ≤ k; reason: false for larger sets: g = Σᵢ xᵢ, Xᵢ ≡ 1, k = 1, n = 5, S = N gives u(S) = 5 > 4; max ∅ is undefined; the proof gives every 0 < |S| ≤ k, more than the |S| = k of Appendix D, and Corollary 1 needs it
--   - generalization: Definition 1: z for every v ≥ 0 with a preimage under g in ℝ₊ⁿ → HasExtendedDiminishingReturns: z for every v = g(z₀, 0) attained on ℝ₊ⁿ⁻¹; reason: a weaker hypothesis (fewer values v), implied by the printed one (proved in a verification file); it is (13) of Appendix A at d = n − 1 and the only form the proof uses
--   - reading: φ, "a minimal element which does not change the function value" (p.11) → φ = 0 (mask, pad); reason: p.11 uses φ = 0 and the domain is ℝ₊; with φ > 0 and Xᵢ < φ possible u is not monotone, and if Xᵢ ≥ φ the shift g(x + φ) reduces to φ = 0
--   - encoding: E[g(·)] of a value function g → Measurable g; reason: what writing the expectations presupposes; excludes only cases where they are undefined
--   - encoding: the replication scores aᵢ = E[g(Xᵢ⁽¹⁾,…,Xᵢ⁽ᵏ⁾,φ,…,φ)] of (7) → the k-fold replica y ↦ g(pad y) is integrable under the k-fold product of Pᵢ, for each i; reason: what (7) presupposes; integrability of every u(S) and of t ↦ g(z, t) follows from it and is not assumed
--   - encoding: N = {1,…,n} with 0 < k ≤ n; nonnegative independent Xᵢ ∼ Pᵢ; g : ℝ₊ⁿ → ℝ₊ → items Fin (m + 1) (n = m + 1); Pᵢ probability measures on ℝ≥0, independence as Measure.pi; g : (Fin (m+1) → ℝ≥0) → ℝ with 0 ≤ g x; reason: n ≥ 1 is forced by 0 < k ≤ n; same instances
--   - encoding: "for convenience, we will assume that the value function g is continuous" (p.36, inside the proof) → no continuity and no attained maximum g^max_{k−1}; reason: assumptions of the printed proof only, not of the lemma
-- source:
--   Sekar, Vojnovic, Yun, A Test Score Based Approach to Stochastic Submodular Optimization, arXiv:1605.07172v4, Lemma 4, p.20; proof in Appendix D, pp.35–38

import Mathlib
import Definitions.Def_TestScoreSubmod_IsSubmodularValue
import Definitions.Def_TestScoreSubmod_IsSymmetricValue
import Definitions.Def_TestScoreSubmod_HasExtendedDiminishingReturns
import Definitions.Def_TestScoreSubmod_utility
import Definitions.Def_TestScoreSubmod_repScore
import Definitions.Def_TestScoreSubmod_IsGoodScores

open scoped NNReal
open MeasureTheory

namespace TestScoreSubmod

/-- **Lemma 4** (Sekar, Vojnovic, Yun, arXiv:1605.07172v4, Lemma 4, p.20; proof in Appendix D,
pp.35–38): if `g : ℝ₊ⁿ → ℝ₊` is a symmetric, monotone submodular value function with the
extended diminishing returns property, the replication test scores are `(1 − 1/e, 4)`-good:

1. `(1 − 1/e) min_{i∈S} aᵢ ≤ u(S)` for every `S` with `|S| = k`, and
2. `u(S) ≤ 4 max_{i∈S} aᵢ` for every nonempty `S` with `|S| ≤ k`.

**Formalization Note** `0 < k ≤ n = m + 1`; performances `Xᵢ ∼ Pᵢ` are independent, in
`ℝ≥0`, with integrable `k`-fold replicas; `Measurable g`. No continuity of `g` and no attained
maximum are assumed (the printed proof assumes both "for convenience", p.36). The sizes of the
sketch condition are those of `IsGoodScores`; "consequently are good test scores" is the same
fact, since the constants are explicit. -/
theorem lemma_4 {m k : ℕ} (hk : 0 < k) (hkn : k ≤ m + 1)
    (g : (Fin (m + 1) → ℝ≥0) → ℝ) (hg0 : ∀ x, 0 ≤ g x) (hmeas : Measurable g)
    (hsym : IsSymmetricValue g) (hmono : Monotone g) (hsub : IsSubmodularValue g)
    (hedr : HasExtendedDiminishingReturns g)
    (P : Fin (m + 1) → Measure ℝ≥0) [∀ i, IsProbabilityMeasure (P i)]
    (hint : ∀ i, Integrable (fun y : Fin k → ℝ≥0 => g (pad y)) (Measure.pi fun _ : Fin k => P i)) :
    IsGoodScores k (1 - 1 / Real.exp 1) 4 (repScore g P k) (utility g P) := by sorry

end TestScoreSubmod
