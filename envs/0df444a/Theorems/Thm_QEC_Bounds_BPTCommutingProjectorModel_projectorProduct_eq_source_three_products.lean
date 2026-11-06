-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_projectorProduct_eq_source_three_products
-- name    : QEC.Bounds.BPTCommutingProjectorModel.projectorProduct_eq_source_three_products
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:25:10.095346+00:00
-- url     : https://prove2.me/theorems/5df84e11-ff04-4672-9167-a0784ba8b562
-- title:
--   BPTCommuting Projector Model: projector Product eq source three products
-- statement:
--   The full code projector is the source product `Pi_AB Pi_BC Pi_CD`.  The three
--   products are regrouped only after their check families have been proved
--   disjoint and after pairwise commutation has been retained explicitly.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L2222-L2246
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L2222-L2246

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

theorem QEC.Bounds.BPTCommutingProjectorModel.projectorProduct_eq_source_three_products
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    M.projectorProduct =
      (M.projectorProductOn (M.interiorChecks region) *
        M.projectorProductOn (M.boundaryChecks region)) *
      M.projectorProductOn (M.exteriorChecks region) := by sorry
