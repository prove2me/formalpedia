-- Prove2me | Theorems.Thm_PeskirShiryaev_SequentialTesting_smooth_fit
-- name    : PeskirShiryaev.SequentialTesting.smooth_fit
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T02:27:41.804871+00:00
-- url     : https://prove2.me/theorems/fe38394f-894e-4466-8e6a-30e7a09ef00a
-- title:
--   Eq. (21.2.41) — smooth fit at both testing boundaries
-- statement:
--   For the finite-horizon Wiener testing value $V$ and its lower and upper contact boundaries $g_0,g_1$, at every time $0\le t<T$ the state derivative exists at both boundaries and satisfies
--   $$\partial_pV(t,g_0(t))=a,\qquad \partial_pV(t,g_1(t))=-b.$$
--   The derivatives agree from the continuation and stopping sides. These are the smooth-fit conditions identified after (21.2.27) and displayed in (21.2.41).
--
--   **Formalization Note** A full derivative is asserted at each boundary, so both traces are present. The terminal time is excluded because the terminal loss has a cusp at $c$.
-- source:
--   Peskir and Shiryaev, Optimal Stopping and Free-Boundary Problems, Birkhäuser Verlag, 2006, DOI 10.1007/978-3-7643-7390-0, pp. 297, 299 / PDF pp. 314, 316, Eqs. (21.2.27), (21.2.41)

import Definitions.Def_PeskirShiryaev_SequentialTesting_BoundaryClass

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace PeskirShiryaev.SequentialTesting

/-- Equations (21.2.27) and (21.2.41): both derivative traces at both
boundaries. HasDerivAt states the common full derivative, with values outside
the continuation interval supplied by the value itself. The cusp at t=T is
excluded, as on the page. -/
theorem smooth_fit {Ω : Type*} [MeasurableSpace Ω]
    (E : Model Ω) (C : Parameters) :
    ∀ t ∈ Ico (0 : ℝ) C.T,
      HasDerivAt (value E C t) C.a (optimalBoundary E C 0 t) ∧
      HasDerivAt (value E C t) (-C.b) (optimalBoundary E C 1 t) := by sorry

end PeskirShiryaev.SequentialTesting
