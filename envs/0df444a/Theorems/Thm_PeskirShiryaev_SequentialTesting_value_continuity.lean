-- Prove2me | Theorems.Thm_PeskirShiryaev_SequentialTesting_value_continuity
-- name    : PeskirShiryaev.SequentialTesting.value_continuity
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T02:27:47.535735+00:00
-- url     : https://prove2.me/theorems/f4c28944-478e-4f63-9e5d-b61c50e688b1
-- title:
--   Eqs. (21.2.8)–(21.2.9) — continuity of the finite-horizon value
-- statement:
--   Let $V(t,p)$ be the posterior stopping value of the finite-horizon Wiener testing experiment, including the absolute clock cost $t$. Then
--   $$V:[0,T]\times[0,1]\longrightarrow\mathbb R\quad\text{is continuous}.$$
--   This is the joint continuity conclusion established by the two continuity statements (21.2.8)–(21.2.9), and includes both deterministic-prior endpoints and the terminal time. It supplies the closed stopping region used in the free-boundary characterization.
--
--   **Formalization Note** Continuity is relative to the closed time-state rectangle. No continuity of $V$ or of an optimal boundary is assumed.
-- source:
--   Peskir and Shiryaev, Optimal Stopping and Free-Boundary Problems, Birkhäuser Verlag, 2006, DOI 10.1007/978-3-7643-7390-0, p. 294 / PDF p. 311, Eqs. (21.2.8)–(21.2.9), introductory sentence of §21.2 paragraph 3

import Definitions.Def_PeskirShiryaev_SequentialTesting_BoundaryClass

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace PeskirShiryaev.SequentialTesting

/-- Equations (21.2.8)-(21.2.9): joint continuity, including both state
endpoints and the finite terminal time. -/
theorem value_continuity {Ω : Type*} [MeasurableSpace Ω]
    (E : Model Ω) (C : Parameters) :
    ContinuousOn (fun z : ℝ × ℝ => value E C z.1 z.2)
      (Icc (0 : ℝ) C.T ×ˢ Icc (0 : ℝ) 1) := by sorry

end PeskirShiryaev.SequentialTesting
