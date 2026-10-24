-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P21_entropy_specializations
-- name    : QAlgorithms.Papers.Independent.Support50.P21.entropy_specializations
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T20:41:23.219782+00:00
-- url     : https://prove2.me/theorems/770a9c7d-0a1b-4f17-8105-a10f99d7f29c
-- title:
--   §III, equations (12)–(16): entropy and mutual-information specializations
-- statement:
--   All systems are nonzero finite-dimensional complex Hilbert spaces, and logarithms have base two.
--
--   Let $\rho$ be a density operator, $\rho_{AB}$ a bipartite density operator, and $\sigma_B$ a density operator. The unconditional entropies satisfy
--
--   $$H_{\min}(\rho)=-D_{\max}(\rho\Vert I)=-\log_2\lambda_{\max}(\rho),\qquad H_{\max}(\rho)=-D_{\min}(\rho\Vert I)=\log_2\operatorname{rank}\rho.$$
--
--   Relative to $\sigma_B$,
--
--   $$H_{\min}(\rho_{AB}\mid\sigma_B)=-D_{\max}(\rho_{AB}\Vert I_A\otimes\sigma_B),$$
--   $$H_{\max}(\rho_{AB}\mid\sigma_B)=-D_{\min}(\rho_{AB}\Vert I_A\otimes\sigma_B)=\log_2\operatorname{Tr}[\pi_{\rho_{AB}}(I_A\otimes\sigma_B)].$$
--
--   Writing $\rho_A,\rho_B$ for the marginals, define $I_{\min/\max}(A:B)=D_{\min/\max}(\rho_{AB}\Vert\rho_A\otimes\rho_B)$. These are the paper's entropy and mutual-information substitutions, with extended logarithms at support failure. The max entropy here is the rank-based order-zero entropy.
-- source:
--   Min- and Max- Relative Entropies and a New Entanglement Monotone, arXiv:0803.2770v3, PDF p. 3, §III, equations (12)–(16): entropy and mutual-information specializations

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P21

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P21

open QAlgorithms QAlgorithms.Entanglement Filter

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

-- Use the accepted declarations directly; no paper-local aliases hide dimension binders.

open QAlgorithms.Papers.Independent.Claimed50.P33
  (FiniteState IsAverageLocalMonotone IsAdaptiveLOCCMonotone)

open QAlgorithms.Papers.Independent.Information100.P63 (Mat)

open QAlgorithms.Papers.Independent.Dependency50.P35 (tr elog maxRelative)

open QAlgorithms.Papers.Independent.Information100.P67 (IsSubnormalized)

open QAlgorithms.Papers.Independent.Information100.P07 (support)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower SupportIncluded)

variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

section Statements

variable [Nonempty I] [Nonempty J]

/-- PDF p.3, (12)–(16): old rank-based Hmax; conditional reference is sigma_B.
The rho_B in the printed first line of (14) is corrected as explained above. -/
theorem entropy_specializations (rho : Mat I) (hrho : IsDensityMatrix rho)
    (rhoAB : Mat (I × J)) (hAB : IsDensityMatrix rhoAB)
    (sigmaB : Mat J) (hB : IsDensityMatrix sigmaB) :
    hMin rho = -maxRelative rho 1 ∧ hMin rho = -elog (largestEigenvalue rho) ∧
    hMax rho = -dMin rho 1 ∧ hMax rho = elog (rho.rank : ℝ) ∧
    conditionalMin rhoAB sigmaB = -maxRelative rhoAB (Matrix.kronecker (1 : Mat I) sigmaB) ∧
    conditionalMax rhoAB sigmaB = -dMin rhoAB (Matrix.kronecker (1 : Mat I) sigmaB) ∧
    conditionalMax rhoAB sigmaB =
      elog (tr (support rhoAB * Matrix.kronecker (1 : Mat I) sigmaB)) ∧
    mutualMin rhoAB = dMin rhoAB (Matrix.kronecker (traceRight rhoAB) (traceLeft rhoAB)) ∧
    mutualMax rhoAB = maxRelative rhoAB (Matrix.kronecker (traceRight rhoAB) (traceLeft rhoAB)) := by sorry

end Statements

end QAlgorithms.Papers.Independent.Support50.P21

end
