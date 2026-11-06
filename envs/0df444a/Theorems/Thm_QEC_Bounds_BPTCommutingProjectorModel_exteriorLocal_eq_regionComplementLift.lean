-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_exteriorLocal_eq_regionComplementLift
-- name    : QEC.Bounds.BPTCommutingProjectorModel.exteriorLocal_eq_regionComplementLift
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:36:24.232756+00:00
-- url     : https://prove2.me/theorems/92e17158-dc62-4b11-8875-19a69eecfbb7
-- title:
--   BPTCommuting Projector Model: exterior Local eq region Complement Lift
-- statement:
--   An actual exterior-local global operator is also a literal complement lift of
--   `M1`, with a `C tensor D` representative whose `C` factor is the identity.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Transport/FourFactor.lean#L171-L214
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Transport/FourFactor.lean#L171-L214

import Definitions.Def_QEC_Bounds_BPTDisentangling_FourFactor
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Transport_FourFactor
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

theorem QEC.Bounds.BPTCommutingProjectorModel.exteriorLocal_eq_regionComplementLift
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (P : Semantics.Operator (M.regionSubsystem (M.exterior region)).selectedSystem) :
    ∃ Z : Semantics.Operator (M.fourFactorD region),
      (M.regionSubsystem (M.exterior region)).extendLocalToRegister P =
        extendComplementToRegister (M.regionSubsystem region)
          (((M.regionSubsystem region).complementFactorization
            (M.regionSubsystem (region ∪ M.externalBoundary region)) (by
              intro site hsite
              exact Finset.mem_union_left _ hsite)).symm.conjOperator
            (TensorProduct.map (1 : Semantics.Operator (M.fourFactorC region)) Z)) := by sorry
