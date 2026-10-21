-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P31_spatialIndex_kernel
-- name    : QAlgorithms.Papers.Independent.Next46.P31.spatialIndex_kernel
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T14:30:25.065037+00:00
-- url     : https://prove2.me/theorems/df6e9ae5-12a9-4e64-a866-8663a103ed94
-- title:
--   Equation (1.9): kernel form of the spatial coherence index
-- statement:
--   Let $d\ge1$, let $H=L^2(\mathbb R^d,dx)$, and let $\rho$ be a positive trace-class operator on $H$ with trace one. Assume that $X_j\rho$ has a trace-class bounded realization for every canonical position coordinate; no momentum regularity is required. Products with unbounded coordinates are interpreted through their forms on the dense operator domains. Write $C_A(\rho)=\|\rho\|_2^{-1}(\sum_j\|[A_j,\rho]\|_2^2)^{1/2}$, $D_A(\rho)=\|\rho\|_2^{-1}(\sum_j\|\{A_j-\operatorname{Tr}(A_j\rho),\rho\}\|_2^2)^{1/2}$, and $S_A=C_A/D_A$ on the nonzero-spread domain; $\|\cdot\|_2$ is the Hilbert–Schmidt norm. Let $K(x,y)$ be any square-integrable kernel representing the actual operator $\rho$ through all its $L^2$ matrix elements. Put $m=(\operatorname{Tr}(X_j\rho))_{j=1}^d$ and assume $D_X(\rho)\ne0$. The two weighted integrands below are integrable, and
--
--   $$
--   S_X(\rho)=\frac{\left(\int |x-y|^2|K(x,y)|^2\,dx\,dy\right)^{1/2}}{\left(\int |x+y-2m|^2|K(x,y)|^2\,dx\,dy\right)^{1/2}}.
--   $$
--
--   The numerator and denominator measure the off-diagonal and centered diagonal widths of the actual kernel; all kernel equalities are interpreted almost everywhere.
-- source:
--   Decoherence rates for Galilean covariant dynamics, arXiv:0710.1344v2, PDF p. 3, Equation (1.9): kernel form of the spatial coherence index

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P31

noncomputable section

open Filter MeasureTheory

open scoped BigOperators ENNReal NNReal ComplexOrder Topology

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

namespace QAlgorithms.Papers.Independent.Next46.P31

open QAlgorithms.PeriodicSchrodinger (Position)

open QAlgorithms.Papers.Independent.Dependency50.P13
  (IsTraceClass IsPositive operatorTrace)

/-- Clark, PDF p.3, (1.9). Both weighted integrability assertions prevent the
Bochner integral's zero default from concealing an undefined kernel width.
Only position products are required, as in the source's spatial-index domain. -/
theorem spatialIndex_kernel {I : Type*} {d : ℕ} (hd : 0 < d)
    (b : HilbertBasis I ℂ (EuclideanSchrodinger d)) (rho : (EuclideanSchrodinger d →L[ℂ] EuclideanSchrodinger d))
    (hrho : IsTraceClass rho ∧ IsPositive rho ∧ operatorTrace b rho = 1) (hregular : ∀ j, RegularProduct (positionGraph j) rho)
    (K : PhasePoint d → ℂ) (hK : RepresentsKernel rho K)
    (hspread : coherenceSpread b positionGraph rho ≠ 0) :
    Integrable (fun z : PhasePoint d => ‖z.1 - z.2‖ ^ 2 * ‖K z‖ ^ 2) ∧
    Integrable (fun z : PhasePoint d =>
      ‖z.1 + z.2 - 2 • positionMean b rho‖ ^ 2 * ‖K z‖ ^ 2) ∧
    coherenceIndex b positionGraph rho =
      Real.sqrt (∫ z : PhasePoint d, ‖z.1 - z.2‖ ^ 2 * ‖K z‖ ^ 2) /
        Real.sqrt (∫ z : PhasePoint d,
          ‖z.1 + z.2 - 2 • positionMean b rho‖ ^ 2 * ‖K z‖ ^ 2) := by sorry

end QAlgorithms.Papers.Independent.Next46.P31

end
