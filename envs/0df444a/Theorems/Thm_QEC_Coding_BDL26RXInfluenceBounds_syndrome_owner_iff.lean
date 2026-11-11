-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXInfluenceBounds_syndrome_owner_iff
-- name    : QEC.Coding.BDL26RXInfluenceBounds.syndrome_owner_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:44:50.220274+00:00
-- url     : https://prove2.me/theorems/b1b1f3f0-3760-4a5e-8dd6-dfc1d67433e3
-- title:
--   BDL26 RXInfluence Bounds: syndrome owner iff
-- statement:
--   The BDL26 RXInfluence Bounds construction uses the syndrome owner iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXInfluenceBounds.lean#L112-L117
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXInfluenceBounds.lean#L112-L117

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCoarseInfluence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformReadoutWeight
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXInfluenceBounds
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXInfluenceBounds
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RXDecoderAdapter BDL26RXCoarseInfluence BDL26BoundedValence
open BDL26GraphQuantitativeBounds BDL26RZMap1CoordinateBridge
open MultiscaleDecoder RXCoarseGraining RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (h : i.val % 2 = 0)

theorem QEC.Coding.BDL26RXInfluenceBounds.syndrome_owner_iff (p : FamilyZ S depth i.succ)
    (v : RXVertex (state S i.val).presentation.X (state S i.val).presentation.Q
      (state S i.val).presentation.Z) :
    p ∈ (rxXiLocalComplex (rxData S depth i h)).syndromeRegion v ↔
      (rxData S depth i h).topCenter p = v := by sorry
