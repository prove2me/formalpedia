-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P09_noEvent_realization
-- name    : QAlgorithms.Papers.Independent.Next46.P09.noEvent_realization
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T14:00:27.576445+00:00
-- url     : https://prove2.me/theorems/bc923e0d-753e-4fda-84b7-07c037895b41
-- title:
--   No-event semigroups admit a C0 contraction implementation
-- statement:
--   Let $H$ be a separable complete complex Hilbert space and let $(T_t)_{t\ge0}$ be a completely positive, trace-nonincreasing dynamical semigroup on the full complex trace class $\mathcal T(H)$, continuous at zero in every bounded trace pairing. Suppose every normalized pure input is sent to a nonnegative multiple, possibly zero, of a normalized pure state. Then there is a strongly continuous contraction semigroup $(C_t)_{t\ge0}$ on $H$ such that
--
--   $$T_t(\rho)=C_t\rho C_t^*\qquad(t\ge0,\ \rho\in\mathcal T(H)).$$
--
--   This identifies the Hilbert-space implementation of no-event evolution. Its uniqueness is not asserted, since scalar phases are invisible on trace-class operators.
-- source:
--   Unbounded generators of dynamical semigroups, arXiv:1707.02266v1, PDF p. 3, Definition II.1, asserted realization of no-event semigroups

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P09

noncomputable section

open Filter MeasureTheory

open scoped BigOperators ENNReal

namespace QAlgorithms.Papers.Independent.Next46.P09

universe u v

open QAlgorithms.Papers.Independent.Dependency50.P13
  (TraceClass IsTraceClass traceNormValue operatorTrace IsPositive)

open QAlgorithms.Papers.Independent.Claimed50.P50 (ContractionSemigroup)

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

variable [CompleteSpace H]

/-- Definition II.1, arXiv:1707.02266v1, PDF p.3: no-event realization.
C is an actual C0 contraction semigroup; no uniqueness of C is asserted. -/
theorem noEvent_realization [TopologicalSpace.SeparableSpace H]
    {I : Type v} (b : HilbertBasis I ℂ H)
    (T : TraceDynamicalSemigroup b) (hNoEvent : IsNoEvent T) :
    ∃ C : ContractionSemigroup H, ∀ (t : NNReal) (rho : TraceClass H),
      (T.maps t rho).val =
        (C.maps t).comp (rho.val.comp (C.maps t).adjoint) := by sorry

end QAlgorithms.Papers.Independent.Next46.P09

end
