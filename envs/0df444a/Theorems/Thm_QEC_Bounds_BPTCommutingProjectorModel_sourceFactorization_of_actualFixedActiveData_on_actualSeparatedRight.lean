-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_sourceFactorization_of_actualFixedActiveData_on_actualSeparatedRight
-- name    : QEC.Bounds.BPTCommutingProjectorModel.sourceFactorization_of_actualFixedActiveData_on_actualSeparatedRight
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T08:03:56.345533+00:00
-- url     : https://prove2.me/theorems/5e1a3bd1-69a2-48af-b60f-aedb9fb73273
-- title:
--   BPTCommuting Projector Model: source Factorization of actual Fixed Active Data on actual Separated Right
-- statement:
--   The BPTCommuting Projector Model construction uses the source Factorization of actual Fixed Active Data on actual Separated Right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Factorizations/ActualDataFactorization.lean#L27-L43
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Factorizations/ActualDataFactorization.lean#L27-L43

import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Factorizations_FixedDataFactorization
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Separation
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Factorizations_ActualDataFactorization
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
set_option maxHeartbeats 2000000
set_option maxRecDepth 2000

theorem QEC.Bounds.BPTCommutingProjectorModel.sourceFactorization_of_actualFixedActiveData_on_actualSeparatedRight
    (M : BPTCommutingProjectorModel L kappa) (left right : Finset L.Site)
    (hseparated : M.ActualProjectorSeparated left right)
    (hdisjoint : Disjoint left right)
    (hactual : M.ActualFixedActiveDataProductRankOneTensor left) :
    ∀ (A : Semantics.Operator (M.regionSubsystem left).selectedSystem)
      (B : Semantics.Operator (M.regionSubsystem right).selectedSystem),
      ∃ coefficient : Complex,
        M.fullCodeProjector * (M.regionSubsystem left).extendLocalToRegister A *
            (M.regionSubsystem right).extendLocalToRegister B * M.fullCodeProjector =
          coefficient •
            (M.fullCodeProjector * (M.regionSubsystem right).extendLocalToRegister B *
              M.fullCodeProjector) := by sorry
