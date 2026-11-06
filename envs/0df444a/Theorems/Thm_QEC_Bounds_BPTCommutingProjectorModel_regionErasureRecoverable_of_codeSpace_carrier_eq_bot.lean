-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_regionErasureRecoverable_of_codeSpace_carrier_eq_bot
-- name    : QEC.Bounds.BPTCommutingProjectorModel.regionErasureRecoverable_of_codeSpace_carrier_eq_bot
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T15:10:57.562685+00:00
-- url     : https://prove2.me/theorems/7977b54b-70fd-4e3b-a90a-e1cbd051809d
-- title:
--   BPTCommuting Projector Model: region Erasure Recoverable of code Space carrier eq bot
-- statement:
--   The BPTCommuting Projector Model construction uses the region Erasure Recoverable of code Space carrier eq bot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Transport/Support.lean#L16-L23
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Transport/Support.lean#L16-L23

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

theorem QEC.Bounds.BPTCommutingProjectorModel.regionErasureRecoverable_of_codeSpace_carrier_eq_bot
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (hcode : M.codeSpace.carrier = ⊥) :
    M.RegionErasureRecoverable region := by sorry
