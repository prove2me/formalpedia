-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CanonicalRootWitnessCounterexample_zero_aux_imbalance_not_boundary
-- name    : QEC.Coding.BDL26CanonicalRootWitnessCounterexample.zero_aux_imbalance_not_boundary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T06:05:22.099603+00:00
-- url     : https://prove2.me/theorems/4a251ec3-4261-4a9b-b98f-49f005e5d413
-- title:
--   BDL26 Canonical Root Witness Counterexample: zero aux imbalance not boundary
-- statement:
--   The directly checkable retained-copy obstruction used at the end.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalRootWitnessCounterexample.lean#L330-L338
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalRootWitnessCounterexample.lean#L330-L338

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

theorem QEC.Coding.BDL26CanonicalRootWitnessCounterexample.zero_aux_imbalance_not_boundary (S : OddScale) (sigma : Word3 S)
    (hx : ∀ x, restrictWordLinear ((LX S).syndromeRegion x) sigma = 0)
    (hq : ∀ q, restrictWordLinear ((LQ S).syndromeRegion q) sigma = 0)
    (z : (state S 2).presentation.Z)
    (hneq : sigma ((A S).induced.zPairEquiv (z,0)).val ≠
      sigma ((A S).induced.zPairEquiv (z,1)).val) :
    sigma ∉ LinearMap.range (d3 S) := by sorry
