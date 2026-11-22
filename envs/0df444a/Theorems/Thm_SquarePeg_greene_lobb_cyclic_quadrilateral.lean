-- Prove2me | Theorems.Thm_SquarePeg_greene_lobb_cyclic_quadrilateral
-- name    : SquarePeg.greene_lobb_cyclic_quadrilateral
-- status  : Open
-- author  : @LG
-- created : 2026-11-21T23:24:00.97638+00:00
-- url     : https://prove2.me/theorems/a7184f4e-7303-45bc-a1ac-652d99e8db48
-- title:
--   Greene-Lobb cyclic quadrilateral peg theorem
-- statement:
--   Every cyclic quadrilateral inscribes in every smooth Jordan curve: for any four distinct concyclic points $q_1,q_2,q_3,q_4$ and any smooth Jordan curve $C$, there is an orientation-preserving similarity (positive scale, rotation, translation) taking all four points into $C$. This resolves the cyclic quadrilateral peg problem.
-- source:
--   Greene-Lobb, Cyclic quadrilaterals and smooth Jordan curves, arXiv:2011.05216, main theorem and definitions (Introduction).

import Mathlib
import Definitions.Def_SchoenfliesCurveCore
import Definitions.Def_SquarePeg_shapes
import Definitions.Def_SquarePeg_classes
import Definitions.Def_SquarePeg_similarity
open Schoenflies

namespace SquarePeg

theorem greene_lobb_cyclic_quadrilateral (C : Set Plane) (hsm : IsSmoothCurve C)
    (q1 q2 q3 q4 : Plane) (hQ : IsCyclicQuadrilateral q1 q2 q3 q4) :
    ∃ (s : ℝ) (θ : ℝ) (t : Plane), 0 < s ∧
      opSim s θ t q1 ∈ C ∧ opSim s θ t q2 ∈ C ∧ opSim s θ t q3 ∈ C ∧ opSim s θ t q4 ∈ C := by sorry

end SquarePeg
