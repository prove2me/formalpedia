-- Prove2me | Theorems.Thm_PersistClust_Count_box_census_arithmetic
-- name    : PersistClust.Count.box_census_arithmetic
-- status  : Proved
-- author  : @fabianroll
-- created : 2026-10-14T10:00:35.18498+00:00
-- url     : https://prove2.me/theorems/50b2764b-5c8b-4e6a-958c-7b45e814f84a
-- title:
--   Box arithmetic: the rank combination over a bar equals the difference of the two open-band censuses
-- statement:
--   Let ι be a type, stage : ℝ → Set ι a stage family and J : ℝ → ι → ι → Prop a relation family satisfying the filtration law hLaw and the tameness module axioms hTame. Let b > d be real levels and η a positive radius with η < (b − d)/2, and assume the four-level genericity: for every level t and every t-cell C, none of b − η, b + η, d + η, d − η equals the birth-supremum of C. Then the box-combination of ranks — (rankFn stage J (b − η) (d + η) − rankFn stage J (b + η) (d + η)) − (rankFn stage J (b − η) (d − η) − rankFn stage J (b + η) (d − η)) — equals the difference of the two open-band censuses: the encard of the (d + η)-cells with birth-supremum in (b − η, b + η) minus the encard of the (d − η)-cells with birth-supremum in (b − η, b + η). Proof: the window-split identity applied at both d + η ≤ b − η and d − η ≤ b − η splits each rank difference into a rank at the higher level plus the encard of the cells whose birth-supremum lies in the window; the ranks at the common level b + η cancel by the ℕ∞ subtraction rule (a + b) − a = b for finite a (the ranks are finite by q-tameness), leaving exactly the two band censuses.
-- source:
--   Support theorem of the persistence-clustering deliverable (RR-6968, Theorem 4.6 cluster): the T3 box-combination arithmetic (t3_box_arith in the rankKill master, Scratch_rankR1 L903-920 — this is also verbatim the statement of the T3a-4 box identity t3_box_identity L923-934, whose one-line proof delegates to t3_box_arith) with its inlined helper chain — t3_rank_meets L468-490, t3_structMap_id L493-496, t3_desc_point L500-521, t3_meets_birthSup L525-576, t3_rank_orig L581-589, t2_qtame L595-609, t3_windowSplit L865-890, t3_add_sub L893-899 — the arithmetic step consumed by the multiplicity unfolding of the matching-census assembly.

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_MatchingCensus

open PersistClust.Count
open scoped ENNReal

namespace PersistClust.Count

theorem box_census_arithmetic {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (hTame : IsTameModule stage J)
    {b d η : ℝ} (hbd : d < b) (hη0 : 0 < η) (hη : η < (b - d) / 2)
    (hgen : ∀ (t : ℝ) (C : comps stage J t), b - η ≠ birthSup hLaw t C ∧
        b + η ≠ birthSup hLaw t C ∧ d + η ≠ birthSup hLaw t C ∧ d - η ≠ birthSup hLaw t C) :
    (rankFn stage J (b - η) (d + η) - rankFn stage J (b + η) (d + η)) -
        (rankFn stage J (b - η) (d - η) - rankFn stage J (b + η) (d - η)) =
      (({C : comps stage J (d + η) | (b - η < birthSup hLaw (d + η) C) ∧
            (birthSup hLaw (d + η) C < b + η)} : Set (comps stage J (d + η))).encard
        - ({C : comps stage J (d - η) | (b - η < birthSup hLaw (d - η) C) ∧
            (birthSup hLaw (d - η) C < b + η)} : Set (comps stage J (d - η))).encard : ℕ∞)
    := by sorry
