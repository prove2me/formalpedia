-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P36_rains_cuttingPlane_bounds
-- name    : QAlgorithms.Papers.Independent.Dependency50.P36.rains_cuttingPlane_bounds
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T16:43:54.950141+00:00
-- url     : https://prove2.me/theorems/380b44d8-d814-4e49-8038-665d4f8a2a78
-- title:
--   Certified cutting-plane cross-entropy bounds
-- statement:
--   Let $\rho$ be a density operator on nonzero finite-dimensional $A\otimes B$, and let $C(\rho)=\inf_{\sigma\in\mathrm{PPT}'}[-\operatorname{Tr}(\rho\ln\sigma)]$, with $+\infty$ on support failure. Choose a nonempty finite list of positive-definite feasible tangent points $\sigma_i=U_i\operatorname{diag}(\lambda_i)U_i^\dagger$ interior to $\mathrm{PPT}'$ in the Hermitian subspace. Define $D(\lambda)_{ab}=(\ln\lambda_a-\ln\lambda_b)/(\lambda_a-\lambda_b)$ for unequal eigenvalues and $D(\lambda)_{aa}=1/\lambda_a$, using the same reciprocal rule for any equal pair, and set $E_i=U_i[D(\lambda_i)\circ(U_i^\dagger\rho U_i)]U_i^\dagger$, where $\circ$ is entrywise multiplication. For any prior bound $b\le C(\rho)$, let $L_b$ be the extended infimum of real $t$ subject to $\sigma\in\mathrm{PPT}'$, $t\ge b$ and nonnegative slacks satisfying
--
--   $$\operatorname{Tr}(E_i\sigma)+t-s_i=-\operatorname{Tr}(\rho\ln\sigma_i)+\operatorname{Tr}(E_i\sigma_i).$$
--
--   For any feasible incumbent $\sigma_*$,
--
--   $$L_b\le C(\rho)\le-\operatorname{Tr}(\rho\ln\sigma_*).$$
--
--   Taking $b=-\infty$ recovers the unconstrained cutting-plane relaxation. These are sound bounds on the unshifted natural-log objective, including singular incumbents; they do not assert algorithmic convergence or termination.
-- source:
--   Non-asymptotic entanglement distillation, arXiv:1706.06221v3, PDF p. 19, Appendix B, Eqs. (70)–(75): rigorous lower/upper objective bounds

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P36

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open Filter MeasureTheory

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

namespace QAlgorithms.Papers.Independent.Dependency50.P36

open QAlgorithms.Papers.Independent.Information100.P03 (partialTransposeB)

open QAlgorithms.Papers.Independent.Information100.P04 (copies)

open QAlgorithms.Papers.Independent.Information100.P21 (FiniteLOCC)

open QAlgorithms.Papers.Independent.Information100.P34 (dephasing)

open QAlgorithms.Papers.Independent.Information100.P63 (testingBeta normalCDF normalQuantile)

open QAlgorithms.Papers.Independent.Information100.P80 (log2)

/-- Appendix B, arXiv:1706.06221v3, PDF pp.19–20, Eqs.(72)–(75).
Nonempty tangent lists and a feasible incumbent bound the unshifted objective (69).
Retaining a valid previous lower bound is sound; no termination is asserted. -/
theorem rains_cuttingPlane_bounds {A B : Type} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] [Nonempty A] [Nonempty B]
    (rho : Matrix (A × B) (A × B) ℂ) (hrho : IsDensityMatrix rho)
    {m : ℕ} (hm : 0 < m) (P : Fin m → TangentPoint A B)
    (incumbent : Matrix (A × B) (A × B) ℂ) (hi : pptPrime incumbent)
    (previous : EReal) (hprevious : previous ≤ crossEntropyOptimum rho) :
    cuttingPlaneOptimum rho P previous ≤ crossEntropyOptimum rho ∧
      crossEntropyOptimum rho ≤ crossEntropy rho incumbent := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P36

end
