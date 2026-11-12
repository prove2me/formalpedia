-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CanonicalRootWitnessCounterexample_rootMask_mid_Q_value
-- name    : QEC.Coding.BDL26CanonicalRootWitnessCounterexample.rootMask_mid_Q_value
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T06:19:27.450168+00:00
-- url     : https://prove2.me/theorems/9ee16b0f-3c1a-40b0-9dfc-0e2c9be09863
-- title:
--   BDL26 Canonical Root Witness Counterexample: root Mask mid Q value
-- statement:
--   Every Q coordinate in that fibre survives the genuine lower owner mask.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalRootWitnessCounterexample.lean#L1936-L1958
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalRootWitnessCounterexample.lean#L1936-L1958

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformIsolation
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalRootWitnessCounterexample
set_option autoImplicit false
attribute [local irreducible] QEC.Coding.BDL26CanonicalHistoryMarks.rootComponent
open QEC QEC.Coding QEC.Coding.BDL26CanonicalRootWitnessCounterexample
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26TannerLocalRegularity BDL26RZLocalReplacement
open BDL26RXDecoderAdapter BDL26RZDecoderAdapter BDL26ReplacementSupport
open BDL26OwnerIncidenceMasks MultiscaleDecoder
open RXCoarseGraining RXCoarseGrainingData
open scoped Classical BigOperators
noncomputable section

theorem QEC.Coding.BDL26CanonicalRootWitnessCounterexample.rootMask_mid_Q_value (S : OddScale)
    (p : LocalRegionIndex ((LQ S).syndromeRegion (q2 S))) :
    rootMaskMidWord S p.val = (lower3 S).val p.val := by sorry
