-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_exteriorCompressionWitness_spec
-- name    : QEC.Bounds.BPTCommutingProjectorModel.exteriorCompressionWitness_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:08:13.627234+00:00
-- url     : https://prove2.me/theorems/5de55b50-3c83-42f0-a954-6e85a4d27b50
-- title:
--   BPTCommuting Projector Model: exterior Compression Witness spec
-- statement:
--   The BPTCommuting Projector Model construction uses the exterior Compression Witness spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Transport/CompressionExteriorWitness.lean#L52-L60
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Transport/CompressionExteriorWitness.lean#L52-L60

import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Transport_ExteriorAction
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Transport_CompressionExteriorWitness
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
set_option maxHeartbeats 500000

theorem QEC.Bounds.BPTCommutingProjectorModel.exteriorCompressionWitness_spec
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (P : Semantics.Operator (M.regionSubsystem (M.exterior region)).selectedSystem) :
    let S := M.regionSubsystem region
    S.registerFactorization.conjOperator
        ((M.regionSubsystem (M.exterior region)).extendLocalToRegister P) =
      TensorProduct.map (1 : Semantics.Operator S.selectedSystem)
        (M.exteriorCompressionComplementAction region P) := by sorry
