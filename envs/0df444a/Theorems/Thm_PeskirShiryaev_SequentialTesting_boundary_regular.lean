-- Prove2me | Theorems.Thm_PeskirShiryaev_SequentialTesting_boundary_regular
-- name    : PeskirShiryaev.SequentialTesting.boundary_regular
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T02:27:32.788909+00:00
-- url     : https://prove2.me/theorems/2ec3dade-22cf-4349-bc5d-a938351f7f1a
-- title:
--   Eqs. (21.2.33)–(21.2.37) — optimal exit and regular boundaries
-- statement:
--   Let $g_0,g_1$ be the contact-set boundaries of the finite-horizon value. The transcendental equations $v_A(B)=b(1-B)$ and $v_A'(B)=-b$ have the unique threshold pair $(A_*,B_*)$ with $0<A_*<c<B_*<1$. Both boundaries are continuous on $[0,T]$, $g_0$ is nondecreasing and $g_1$ nonincreasing, and
--   $$A_*\le g_0(t)<c<g_1(t)\le B_*\quad(0\le t<T),\qquad g_0(T)=g_1(T)=c.$$
--   For each starting clock $t\in[0,T]$ and prior $p\in[0,1]$, the exit time
--   $$\tau_*^{t,p}=\inf\{0\le u\le T-t:\Pi^p_u\notin(g_0(t+u),g_1(t+u))\}$$
--   is admissible and satisfies $E_p[t+\tau_*^{t,p}+H(\Pi^p_{\tau_*^{t,p}})]=V(t,p)$. This provides the optimal boundary pair before the coupled equations characterize it uniquely.
--
--   **Formalization Note** The threshold pair is specified by the root equations recalled after (21.2.37); the defective piecewise value formula (21.1.13) is not used. Empty exit sets receive the remaining horizon. Increasing and decreasing mean non-strict monotonicity.
-- source:
--   Peskir and Shiryaev, Optimal Stopping and Free-Boundary Problems, Birkhäuser Verlag, 2006, DOI 10.1007/978-3-7643-7390-0, pp. 298–299 / PDF pp. 315–316, Eqs. (21.2.33)–(21.2.37), with the threshold characterization recalled after (21.2.37)

import Definitions.Def_PeskirShiryaev_SequentialTesting_BoundaryClass

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace PeskirShiryaev.SequentialTesting

/-- Equations (21.2.33)-(21.2.37), including the root characterization
of A* and B* recalled immediately below (21.2.37). -/
theorem boundary_regular {Ω : Type*} [MeasurableSpace Ω]
    (E : Model Ω) (C : Parameters) :
    ThresholdPair C (lowerThreshold C) (upperThreshold C) ∧
    (∀ A B : ℝ, ThresholdPair C A B →
      A = lowerThreshold C ∧ B = upperThreshold C) ∧
    BoundaryClass C (optimalBoundary E C) ∧
    (∀ t ∈ Icc (0 : ℝ) C.T, ∀ p ∈ Icc (0 : ℝ) 1,
      let τ := exitTime E C (optimalBoundary E C) t p
      Admissible E C (C.T - t) τ ∧
        stoppingCost E C t p τ = value E C t p) := by sorry

end PeskirShiryaev.SequentialTesting
