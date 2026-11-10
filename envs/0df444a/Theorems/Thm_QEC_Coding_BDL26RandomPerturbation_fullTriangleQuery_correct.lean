-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_fullTriangleQuery_correct
-- name    : QEC.Coding.BDL26RandomPerturbation.fullTriangleQuery_correct
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T04:00:17.077143+00:00
-- url     : https://prove2.me/theorems/3f613624-4b2a-47cb-b9cb-1ec12d1da167
-- title:
--   BDL26 Random Perturbation: full Triangle Query correct
-- statement:
--   The BDL26 Random Perturbation construction uses the full Triangle Query correct property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/FullEventQuery.lean#L45-L52
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/FullEventQuery.lean#L45-L52

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_AnchorQuery
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_GridEnumerationQuery
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_SnapshotQuery
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EventQuery
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FullEventQuery
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction.SphericalCap

theorem QEC.Coding.BDL26RandomPerturbation.fullTriangleQuery_correct (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r lambda : ℝ) (e : Event P J r) (a : e.val)
    (p : eventSupport P J r e → Space) (center : Space) :
    (fullTriangleQuery P J r lambda e a p center).1 = true ↔
      (fun i => p (eventVertex P J r e a i)) ∈
        triangleHit (fun i => lambda • ((1/2 : ℝ) • J (triangleVertex P a.val i))) center 2 := by sorry
