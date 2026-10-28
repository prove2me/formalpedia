-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P21_smooth_specializations
-- name    : QAlgorithms.Papers.Independent.Support50.P21.smooth_specializations
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-23T20:52:47.430718+00:00
-- url     : https://prove2.me/theorems/7f6acc2f-f915-4d3e-ad3b-2a9a89760272
-- title:
--   §III/§VI: smooth entropy and mutual-information specializations
-- statement:
--   All systems are nonzero finite-dimensional complex Hilbert spaces, and logarithms have base two.
--
--   Let $\varepsilon\ge0$, let $\rho$ and $\rho_{AB}$ be density operators, and let $\sigma_B$ be a density operator. The smooth entropy substitutions are
--
--   $$H_{\min}^{\varepsilon}(\rho)=-D_{\max}^{\varepsilon}(\rho\Vert I),\qquad H_{\max}^{\varepsilon}(\rho)=-D_{\min}^{\varepsilon}(\rho\Vert I),$$
--   $$H_{\min}^{\varepsilon}(\rho_{AB}\mid\sigma_B)=-D_{\max}^{\varepsilon}(\rho_{AB}\Vert I_A\otimes\sigma_B),\quad H_{\max}^{\varepsilon}(\rho_{AB}\mid\sigma_B)=-D_{\min}^{\varepsilon}(\rho_{AB}\Vert I_A\otimes\sigma_B).$$
--
--   For the original marginals $\rho_A,\rho_B$, define $I_{\min/\max}^{\varepsilon}(A:B)=D_{\min/\max}^{\varepsilon}(\rho_{AB}\Vert\rho_A\otimes\rho_B)$. Only the first argument is smoothed; the comparison operator is held fixed. These are definitions with the paper's trace-norm smoothing and rank-based max-entropy convention.
-- source:
--   Min- and Max- Relative Entropies and a New Entanglement Monotone, arXiv:0803.2770v3, PDF p. 4, §III/§VI: smooth entropy and mutual-information specializations

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

/-- PDF pp.4,7: literal smooth substitutions, retaining the original marginals
and the paper's rank-based max convention. These are definitional identities. -/
theorem smooth_specializations (eps : ℝ) (heps : 0 ≤ eps)
    (rho : Mat I) (hrho : IsDensityMatrix rho)
    (rhoAB : Mat (I × J)) (hAB : IsDensityMatrix rhoAB)
    (sigmaB : Mat J) (hB : IsDensityMatrix sigmaB) :
    smoothHMin eps rho = -traceSmoothMax eps rho 1 ∧
    smoothHMax eps rho = -traceSmoothMin eps rho 1 ∧
    smoothConditionalMin eps rhoAB sigmaB =
      -traceSmoothMax eps rhoAB (Matrix.kronecker (1 : Mat I) sigmaB) ∧
    smoothConditionalMax eps rhoAB sigmaB =
      -traceSmoothMin eps rhoAB (Matrix.kronecker (1 : Mat I) sigmaB) ∧
    smoothMutualMin eps rhoAB =
      traceSmoothMin eps rhoAB (Matrix.kronecker (traceRight rhoAB) (traceLeft rhoAB)) ∧
    smoothMutualMax eps rhoAB =
      traceSmoothMax eps rhoAB (Matrix.kronecker (traceRight rhoAB) (traceLeft rhoAB)) := by sorry

end Statements

end QAlgorithms.Papers.Independent.Support50.P21

end
