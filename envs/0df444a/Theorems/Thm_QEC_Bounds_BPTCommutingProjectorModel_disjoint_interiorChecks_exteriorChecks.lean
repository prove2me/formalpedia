-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_disjoint_interiorChecks_exteriorChecks
-- name    : QEC.Bounds.BPTCommutingProjectorModel.disjoint_interiorChecks_exteriorChecks
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:24:42.706888+00:00
-- url     : https://prove2.me/theorems/a1a2f701-e7d2-45c4-860c-ca1ade1f7097
-- title:
--   BPTCommuting Projector Model: disjoint interior Checks exterior Checks
-- statement:
--   The `A`-touching and `D`-touching check families are disjoint.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L1937-L1950
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L1937-L1950

import Definitions.Def_QEC_Bounds_BPTDisentangling_InteractionAlgebra
import Definitions.Def_QEC_Bounds_BPTDisentangling_FourFactor
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

theorem QEC.Bounds.BPTCommutingProjectorModel.disjoint_interiorChecks_exteriorChecks
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    Disjoint (M.interiorChecks region) (M.exteriorChecks region) := by sorry
