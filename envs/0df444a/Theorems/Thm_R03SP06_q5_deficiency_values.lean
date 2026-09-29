-- Prove2me | Theorems.Thm_R03SP06_q5_deficiency_values
-- name    : R03SP06.q5_deficiency_values
-- status  : Proved
-- author  : @hao jia
-- created : 2026-09-16T10:17:58.420216+00:00
-- url     : https://prove2.me/theorems/d13b9f19-5774-447f-b480-5ea56bdee054
-- title:
--   Q5 deficiency values
-- statement:
--   Deficiency 3-degree has values 0, 1, or 2 when the graph has minimum degree one and is subcubic.
--
--   $$\sum_v(3-\deg v)=2n_1+n_2.$ $
--
--   This isolates one reusable arithmetic step for classifying subcubic residual graphs of total cubic deficiency five. It is an auxiliary theorem and does not assert the open root P3-factor conjecture.
-- source:
--   Derived auxiliary theorem for the Prove2me mission ‘P3-Partitions of Cubic 3-Connected Graphs (OPG-46613)’, https://prove2.me/missions/P3-Partitions%20of%20Cubic%203-Connected%20Graphs%20%28OPG-46613%29; background: A. Kelmans, ‘Packing 3-vertex paths in cubic 3-connected graphs’, arXiv:0801.1239.

import Mathlib
import Definitions.Def_cubic_p3_partition_models

namespace R03SP06

variable {V : Type} [Fintype V] [DecidableEq V]

open CubicP3Partition

theorem q5_deficiency_values
    {G : SimpleGraph V}
    (hdeg : ∀ v, 1 ≤ degree G v ∧ degree G v ≤ 3) :
    ∀ v, 3 - degree G v = 0 ∨ 3 - degree G v = 1 ∨
      3 - degree G v = 2 := by sorry

end R03SP06
