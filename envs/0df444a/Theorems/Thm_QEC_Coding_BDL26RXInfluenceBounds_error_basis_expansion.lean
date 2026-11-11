-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXInfluenceBounds_error_basis_expansion
-- name    : QEC.Coding.BDL26RXInfluenceBounds.error_basis_expansion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T06:59:45.885399+00:00
-- url     : https://prove2.me/theorems/59b2ec99-7e0d-4c62-9b72-6c324e26ed0c
-- title:
--   BDL26 RXInfluence Bounds: error basis expansion
-- statement:
--   Actual finite coordinate expansion, used only for the linear differential.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXInfluenceBounds.lean#L195-L198
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXInfluenceBounds.lean#L195-L198

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

theorem QEC.Coding.BDL26RXInfluenceBounds.error_basis_expansion (e : (indexedFamily S depth).Cochain1 i.succ) :
    e = ∑ q, e q • (canonicalBasisWord (F := BDL26Field) q) := by sorry
