-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_commute_of_disjoint_region_support
-- name    : QEC.Bounds.BPTCommutingProjectorModel.commute_of_disjoint_region_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:35:39.304013+00:00
-- url     : https://prove2.me/theorems/f9359d8a-6905-497e-887c-4d3efb7b57e1
-- title:
--   BPTCommuting Projector Model: commute of disjoint region support
-- statement:
--   Concrete local extensions on disjoint site regions commute.  The proof uses
--   the selected/complement tensor factorization of `left`: `right` is lifted to
--   the literal complement and the two maps become `A tensor 1` and `1 tensor B`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Transport/Support.lean#L30-L74
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Transport/Support.lean#L30-L74

import Definitions.Def_QEC_Bounds_BPTDisentangling_FourFactor
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Transport_Support
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

theorem QEC.Bounds.BPTCommutingProjectorModel.commute_of_disjoint_region_support
    (M : BPTCommutingProjectorModel L kappa) (left right : Finset L.Site)
    (hdisjoint : Disjoint left right)
    {A B : Semantics.Operator L.Register}
    (hA : (M.regionSubsystem left).OperatorSupportedOnRegister A)
    (hB : (M.regionSubsystem right).OperatorSupportedOnRegister B) :
    Commute A B := by sorry
