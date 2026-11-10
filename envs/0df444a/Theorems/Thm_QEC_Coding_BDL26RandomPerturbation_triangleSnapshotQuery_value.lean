-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_triangleSnapshotQuery_value
-- name    : QEC.Coding.BDL26RandomPerturbation.triangleSnapshotQuery_value
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T03:59:42.555505+00:00
-- url     : https://prove2.me/theorems/88d59eba-5dd2-4e8a-8adc-df32fb4cc85a
-- title:
--   BDL26 Random Perturbation: triangle Snapshot Query value
-- statement:
--   The BDL26 Random Perturbation construction uses the triangle Snapshot Query value property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/SnapshotQuery.lean#L47-L53
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/SnapshotQuery.lean#L47-L53

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ExactRealProgram
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Events
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_SnapshotQuery
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction.SphericalCap

theorem QEC.Coding.BDL26RandomPerturbation.triangleSnapshotQuery_value (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r lambda : ℝ) (e : Event P J r) (a : e.val)
    (p : eventSupport P J r e → Space) :
    (triangleSnapshotQuery P J r lambda e a p).1 =
      fun i => lambda • ((1/2 : ℝ) • J (triangleVertex P a.val i))+p (eventVertex P J r e a i) := by sorry
