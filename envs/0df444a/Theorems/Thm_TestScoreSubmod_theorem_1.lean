-- Prove2me | Theorems.Thm_TestScoreSubmod_theorem_1
-- name    : TestScoreSubmod.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:49:08.611674+00:00
-- url     : https://prove2.me/theorems/dc0f3dfd-0107-42bf-816e-5a0c6cfd91b7
-- title:
--   Theorem 1: the top $k$ items by replication test score give a $\frac{1-1/e}{5-1/e}$-approximation
-- statement:
--   Let $N=\{1,\dots,n\}$ and $0<k\le n$. Let $g:\mathbb R_+^n\to\mathbb R_+$ be a measurable, symmetric, monotone submodular value function with the extended diminishing returns property, and let $X_1,\dots,X_n$ be independent nonnegative performances, $X_i\sim P_i$ (not necessarily identically distributed), whose $k$-fold replicas have integrable value. Let $u(S)=\mathbb E[g(M_S(X))]$ be the utility and
--
--   $$
--   a_i=\mathbb E\bigl[g(X_i^{(1)},\dots,X_i^{(k)},0,\dots,0)\bigr]
--   $$
--
--   the replication test scores, with $X_i^{(1)},\dots,X_i^{(k)}$ independent copies of $X_i$. If $S$ is a set of $k$ items with the largest replication scores (greedy selection in decreasing order, under any tie-breaking), then for every set $T$ with $|T|=k$, in particular for an optimum set,
--
--   $$
--   u(S)\ge\frac{1-1/e}{5-1/e}\,u(T).
--   $$
--
--   Selecting items by a score computed from each item's own distribution alone is thus a constant-factor approximation for stochastic monotone submodular maximization under a cardinality constraint, for this class of value functions.
--
--   Differences from the source:
--
--   - reading: φ, "a minimal element which does not change the function value" (p.11) → φ = 0 (mask, pad); reason: p.11 uses φ = 0 and the domain is ℝ₊; with φ > 0 and Xᵢ < φ possible u is not monotone, and if Xᵢ ≥ φ the shift g(x + φ) reduces to φ = 0
--   - generalization: Definition 1: z for every v ≥ 0 with a preimage under g in ℝ₊ⁿ → HasExtendedDiminishingReturns: z for every v = g(z₀, 0) attained on ℝ₊ⁿ⁻¹; reason: a weaker hypothesis (fewer values v), implied by the printed one (proved in a verification file); it is (13) of Appendix A at d = n − 1 and the only form the proof uses
--   - reading: the greedy selection of items in decreasing order of replication test scores; the optimal value → every S with IsTopK (repScore g P k) k S; every T with |T| = k; reason: covers every tie-breaking rule and, since an optimum exists among finitely many sets, the optimal value
--   - encoding: E[g(·)] of a value function g → Measurable g; reason: what writing the expectations presupposes; excludes only cases where they are undefined
--   - encoding: the replication scores aᵢ = E[g(Xᵢ⁽¹⁾,…,Xᵢ⁽ᵏ⁾,φ,…,φ)] of (7) → the k-fold replica y ↦ g(pad y) is integrable under the k-fold product of Pᵢ, for each i; reason: what (7) presupposes; integrability of every u(S) and of t ↦ g(z, t) follows from it and is not assumed
--   - encoding: N = {1,…,n} with 0 < k ≤ n; nonnegative independent Xᵢ ∼ Pᵢ; g : ℝ₊ⁿ → ℝ₊ → items Fin (m + 1) (n = m + 1); Pᵢ probability measures on ℝ≥0, independence as Measure.pi; g : (Fin (m+1) → ℝ≥0) → ℝ with 0 ≤ g x; reason: n ≥ 1 is forced by 0 < k ≤ n; same instances
-- source:
--   Sekar, Vojnovic, Yun, A Test Score Based Approach to Stochastic Submodular Optimization, arXiv:1605.07172v4, Theorem 1, pp.17–18; proof p.20 (Corollary 1 and Lemma 4) and Appendix D, pp.35–38

import Mathlib
import Definitions.Def_TestScoreSubmod_IsSubmodularValue
import Definitions.Def_TestScoreSubmod_IsSymmetricValue
import Definitions.Def_TestScoreSubmod_HasExtendedDiminishingReturns
import Definitions.Def_TestScoreSubmod_utility
import Definitions.Def_TestScoreSubmod_repScore
import Definitions.Def_TestScoreSubmod_IsTopK

open scoped NNReal
open MeasureTheory

namespace TestScoreSubmod

/-- **Theorem 1** (Sekar, Vojnovic, Yun, arXiv:1605.07172v4, Theorem 1, pp.17–18): if the utility
set function is the expected value of a symmetric, monotone submodular value function with the
extended diminishing returns property, then greedy selection of `k` items in decreasing order of
replication test scores has utility at least `(1 − 1/e)/(5 − 1/e)` times the optimal value.

For `0 < k ≤ n = m + 1`, every nonnegative, measurable, symmetric, monotone submodular `g` with
extended diminishing returns, every family of independent performance laws `Pᵢ` on `ℝ₊` with
integrable `k`-fold replicas, every top-`k` set `S` for the replication scores `aᵢ` (any
tie-breaking) and every `T` with `|T| = k`:

`(1 − 1/e)/(5 − 1/e) · u(T) ≤ u(S)`.

**Formalization Note** Items are `Fin (m + 1)` (`n ≥ 1` follows from `0 < k ≤ n`), performances
`ℝ≥0`, `φ = 0`; `g (Fin.snoc z t)` is `g(z, t)`. Extended diminishing returns is Definition 1
with the preimage taken in `n − 1` coordinates (implied by the printed form). `Measurable g` and
the integrability of the `k` replicas are what the expectations presuppose; the integrability of
`u(S)` follows. No continuity, attained maximum, `n ≥ 2k`, `g(0) = 0` or identical distributions
is assumed. -/
theorem theorem_1 {m k : ℕ} (hk : 0 < k) (hkn : k ≤ m + 1)
    (g : (Fin (m + 1) → ℝ≥0) → ℝ) (hg0 : ∀ x, 0 ≤ g x) (hmeas : Measurable g)
    (hsym : IsSymmetricValue g) (hmono : Monotone g) (hsub : IsSubmodularValue g)
    (hedr : HasExtendedDiminishingReturns g)
    (P : Fin (m + 1) → Measure ℝ≥0) [∀ i, IsProbabilityMeasure (P i)]
    (hint : ∀ i, Integrable (fun y : Fin k → ℝ≥0 => g (pad y)) (Measure.pi fun _ : Fin k => P i))
    (S : Finset (Fin (m + 1))) (hS : IsTopK (repScore g P k) k S)
    (T : Finset (Fin (m + 1))) (hT : T.card = k) :
    (1 - 1 / Real.exp 1) / (5 - 1 / Real.exp 1) * utility g P T ≤ utility g P S := by sorry

end TestScoreSubmod
