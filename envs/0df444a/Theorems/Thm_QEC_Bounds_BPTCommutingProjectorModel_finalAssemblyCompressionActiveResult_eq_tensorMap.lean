-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_finalAssemblyCompressionActiveResult_eq_tensorMap
-- name    : QEC.Bounds.BPTCommutingProjectorModel.finalAssemblyCompressionActiveResult_eq_tensorMap
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-18T05:23:52.318868+00:00
-- url     : https://prove2.me/theorems/d733f23a-a40c-4ad5-a1ff-b5868e63abea
-- title:
--   BPTCommuting Projector Model: final Assembly Compression Active Result eq tensor Map
-- statement:
--   The BPTCommuting Projector Model construction uses the final Assembly Compression Active Result eq tensor Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Transport/CompressionExteriorActiveStatement.lean#L50-L67
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Transport/CompressionExteriorActiveStatement.lean#L50-L67

import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Transport_ExteriorAction
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Transport_CompressionExteriorCoordinates
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Transport_CompressionExteriorActiveStatement
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
set_option maxHeartbeats 800000

theorem QEC.Bounds.BPTCommutingProjectorModel.finalAssemblyCompressionActiveResult_eq_tensorMap
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (nB nC : Nat)
    (WB : Submodule (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region))
    (WC : Submodule (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region))
    (Z : Semantics.Operator (M.fourFactorD region)) :
    M.finalAssemblyCompressionActiveResult region nB nC WB WC Z =
      (show Semantics.Operator (M.FinalAssemblyCompressionDomain region nB nC WB WC) from
        TensorProduct.map (1 : Semantics.Operator
          (Semantics.CompositeSystem
            (Semantics.CompositeSystem (M.fourFactorA region) (WB.restrictScalars Complex))
            (isotypicLiftedMultiplicity.{0} nB)))
          (TensorProduct.map (1 : Semantics.Operator (WC.restrictScalars Complex))
            (TensorProduct.map
              (1 : Semantics.Operator (isotypicLiftedMultiplicity.{0} nC)) Z))) := by sorry
