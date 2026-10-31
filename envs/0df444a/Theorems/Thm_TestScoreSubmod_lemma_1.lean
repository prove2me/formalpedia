-- Prove2me | Theorems.Thm_TestScoreSubmod_lemma_1
-- name    : TestScoreSubmod.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:48:48.615544+00:00
-- url     : https://prove2.me/theorems/65019f3b-72b4-412f-85bb-d668d6e83345
-- title:
--   Lemma 1: the expected value of a monotone submodular value function is a monotone submodular set function
-- statement:
--   Let $N$ be a finite set of items, $g:\mathbb R_+^{N}\to\mathbb R_+$ a monotone submodular value function, and $X_i\sim P_i$ independent nonnegative performances such that every $g(M_S(X))$ is integrable. Then the set function
--
--   $$
--   u(S)=\mathbb E\bigl[g(M_S(X))\bigr],\qquad S\subseteq N,
--   $$
--
--   takes values in $\mathbb R_+$, is monotone ($S\subseteq T\Rightarrow u(S)\le u(T)$) and is submodular:
--
--   $$
--   u(S\cup T)+u(S\cap T)\le u(S)+u(T)\quad\text{for all }S,T\subseteq N.
--   $$
--
--   This justifies treating the stochastic objective (5) as a monotone submodular maximization problem. The paper borrows it from Asadpour and Nazerzadeh (2016).
--
--   Differences from the source:
--
--   - reading: φ, "a minimal element which does not change the function value" (p.11) → φ = 0 (mask, pad); reason: p.11 uses φ = 0 and the domain is ℝ₊; with φ > 0 and Xᵢ < φ possible u is not monotone, and if Xᵢ ≥ φ the shift g(x + φ) reduces to φ = 0
--   - encoding: u(S) = E[g(M_S(X))] for all S (4) → x ↦ g(M_S x) integrable under Measure.pi P for every S; reason: what writing the expectation presupposes; excludes only undefined cases
--   - encoding: ground set N, nonnegative independent Xᵢ ∼ Pᵢ, g : ℝⁿ → ℝ₊ → a finite type ι, probability measures Pᵢ on ℝ≥0, Measure.pi P, 0 ≤ g x; reason: same instances
-- source:
--   Sekar, Vojnovic, Yun, A Test Score Based Approach to Stochastic Submodular Optimization, arXiv:1605.07172v4, Lemma 1, p.11

import Mathlib
import Definitions.Def_TestScoreSubmod_IsSubmodularValue
import Definitions.Def_TestScoreSubmod_utility
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular

open scoped NNReal
open MeasureTheory

namespace TestScoreSubmod

/-- **Lemma 1** (Sekar, Vojnovic, Yun, arXiv:1605.07172v4, Lemma 1, p.11; borrowed from
Asadpour and Nazerzadeh 2016, Lemma 3): if `g` is a monotone submodular value function, the set
function `u(S) = E[g(M_S(X))]` of eq. (4) is a monotone submodular set function, with values in
`ℝ₊`.

**Formalization Note** Items are a finite type `ι`, performances `ℝ≥0`, `φ = 0`. The laws
`P i` are probability measures and the performances are independent (`Measure.pi P`).
`g ≥ 0` is the codomain `ℝ₊` of a value function (p.10). The integrability of every
`x ↦ g (M_S x)` is what writing `E[·]` presupposes. -/
theorem lemma_1 {ι : Type} [Fintype ι] [DecidableEq ι] (g : (ι → ℝ≥0) → ℝ)
    (hg0 : ∀ x, 0 ≤ g x) (hmono : Monotone g) (hsub : IsSubmodularValue g)
    (P : ι → Measure ℝ≥0) [∀ i, IsProbabilityMeasure (P i)]
    (hint : ∀ S : Finset ι, Integrable (fun x => g (mask S x)) (Measure.pi P)) :
    (∀ S, 0 ≤ utility g P S) ∧ Monotone (utility g P) ∧
      NonmonotoneSubmod.Shared.Submodular (utility g P) := by sorry

end TestScoreSubmod
