-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_secondCut_compressed_scalar_for_left_subtype_probe
-- name    : QEC.Bounds.BPTCommutingProjectorModel.secondCut_compressed_scalar_for_left_subtype_probe
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T14:42:41.557205+00:00
-- url     : https://prove2.me/theorems/127dbb37-1393-4c3e-bd62-a81fa0dd4bbb
-- title:
--   BPTCommuting Projector Model: second Cut compressed scalar for left subtype probe
-- statement:
--   The physical hM relation compresses to every literal probe on the selected
--   left isotypic subtype.  This is the source `Pi_AB'` scalar equation before
--   the later block transport chooses a particular `X`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/ScalarCompression/Coordinates.lean#L29-L76
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/ScalarCompression/Coordinates.lean#L29-L76

import Definitions.Def_QEC_Bounds_BPTDisentangling_SecondCut_Core
import Definitions.Def_QEC_Bounds_BPTDisentangling_ScalarCompression_Coordinates
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
set_option maxHeartbeats 300000

theorem QEC.Bounds.BPTCommutingProjectorModel.secondCut_compressed_scalar_for_left_subtype_probe
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (hM : M.RegionErasureRecoverable region)
    (H : Submodule Complex (M.fourFactorB region))
    (J : Semantics.CompositeSystem
        (Semantics.CompositeSystem (M.fourFactorA region) H)
        (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region)) →ₗ[Complex]
      Semantics.CompositeSystem
        (Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region))
        (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region)))
    (hJ : J = tensorTripleSubtypeEmbedding (A := M.fourFactorA region)
      (C := Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region)) H)
    (Rcompressed : Semantics.Operator
      (Semantics.CompositeSystem
        (Semantics.CompositeSystem (M.fourFactorA region) H)
        (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))))
    (hreconstruct : M.secondCutCodeLift region =
      J.comp (Rcompressed.comp (LinearMap.adjoint J)))
    (Esub : Semantics.Operator
      (Semantics.CompositeSystem (M.fourFactorA region) H)) :
    ∃ scalar : Complex,
      Rcompressed *
          overlapLiftLeft
            (C := Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region)) Esub *
          Rcompressed =
        scalar • Rcompressed := by sorry
