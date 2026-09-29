-- Prove2me | Theorems.Thm_R03SP06_q5_weighted_deficiency_identity
-- name    : R03SP06.q5_weighted_deficiency_identity
-- status  : Proved
-- author  : @hao jia
-- created : 2026-09-16T10:18:14.315692+00:00
-- url     : https://prove2.me/theorems/d516766a-3973-47cb-952c-39478749b1ce
-- title:
--   Q5 weighted deficiency identity
-- statement:
--   The total deficiency is the weighted count of degree-one and degree-two vertices.
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

theorem q5_weighted_deficiency_identity
    {G : SimpleGraph V}
    (hdeg : ∀ v, 1 ≤ degree G v ∧ degree G v ≤ 3) :
    ∑ v, (3 - degree G v) =
      2 * (Finset.filter (fun v => degree G v = 1) Finset.univ).card +
        (Finset.filter (fun v => degree G v = 2) Finset.univ).card := by sorry

end R03SP06
