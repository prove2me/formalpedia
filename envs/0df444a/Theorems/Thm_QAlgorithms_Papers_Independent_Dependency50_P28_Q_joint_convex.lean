-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P28_Q_joint_convex
-- name    : QAlgorithms.Papers.Independent.Dependency50.P28.Q_joint_convex
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T17:54:31.482209+00:00
-- url     : https://prove2.me/theorems/d24c655b-aee7-4334-8200-a5a7eb530d11
-- title:
--   Joint convexity of the raw sandwiched trace
-- statement:
--   Let (ρᵢ,σᵢ) be a finite family of positive semidefinite pairs, each with nested supports, and let pᵢ≥0 sum to one. For α>1,
--
--   Write $Q_\alpha(\rho\Vert\sigma)=\operatorname{Tr}(\sigma^{(1-\alpha)/(2\alpha)}\rho\sigma^{(1-\alpha)/(2\alpha)})^\alpha$ and $F_\alpha=\log Q_\alpha$. Powers are evaluated only on positive eigenvalues and are zero on the kernel, even at exponent zero; scalar logarithms satisfy $\log0=-\infty$.
--
--   $$
--   Q_\alpha\!\left(\sum_i p_i\rho_i\middle\Vert\sum_i p_i\sigma_i\right)\leq\sum_i p_iQ_\alpha(\rho_i\Vert\sigma_i).
--   $$
--
--   This bounds a finite convex mixture by the mixture of the individual raw-trace values.
-- source:
--   Quantum hypothesis testing and the operational interpretation of the quantum Renyi relative entropies, arXiv:1309.3228v5, PDF p. 8, Corollary III.16 (joint convexity)

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P28

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P28

open scoped Matrix ComplexConjugate ComplexOrder BigOperators

open Filter QAlgorithms

open QAlgorithms.Papers.Independent.Information100.P60 (Mat copies)

open QAlgorithms.Papers.Independent.Information100.P07 (support positivePart positiveProjection)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- arXiv:1309.3228v5, PDF p.8: Joint convexity of the raw sandwiched trace. The display omits the order range; Corollary III.15 and the proof supply alpha>1. Empty index types cannot carry the required probability weights. -/
theorem Q_joint_convex {K : Type} [Fintype K] (rho sigma : K → Mat I)
    (hrho : ∀ i, (rho i).PosSemidef) (hsigma : ∀ i, (sigma i).PosSemidef)
    (hsupp : ∀ i, SupportLE (rho i) (sigma i)) (p : K → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) (alpha : ℝ) (ha : 1 < alpha) :
    Q alpha (∑ i, (p i : ℂ) • rho i) (∑ i, (p i : ℂ) • sigma i) ≤
      ∑ i, p i * Q alpha (rho i) (sigma i) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P28

end
