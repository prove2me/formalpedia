-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_regionFactorization_conj_exteriorLocal
-- name    : QEC.Bounds.BPTCommutingProjectorModel.regionFactorization_conj_exteriorLocal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:22:40.768408+00:00
-- url     : https://prove2.me/theorems/f21f594e-30e8-4e3f-9bef-dc2e08576832
-- title:
--   BPTCommuting Projector Model: region Factorization conj exterior Local
-- statement:
--   The BPTCommuting Projector Model construction uses the region Factorization conj exterior Local property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Transport/ExteriorAction.lean#L22-L53
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Transport/ExteriorAction.lean#L22-L53

import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Transport_FourFactor
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Transport_ExteriorAction
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

theorem QEC.Bounds.BPTCommutingProjectorModel.regionFactorization_conj_exteriorLocal
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (P : Semantics.Operator (M.regionSubsystem (M.exterior region)).selectedSystem) :
    ∃ Z : Semantics.Operator (M.fourFactorD region),
      let S := M.regionSubsystem region
      let T := M.regionSubsystem (region ∪ M.externalBoundary region)
      let splitCD := S.complementFactorization T (by
        intro site hsite
        exact Finset.mem_union_left _ hsite)
      S.registerFactorization.conjOperator
          ((M.regionSubsystem (M.exterior region)).extendLocalToRegister P) =
        TensorProduct.map (1 : Semantics.Operator S.selectedSystem)
          (splitCD.symm.conjOperator
            (TensorProduct.map (1 : Semantics.Operator (M.fourFactorC region)) Z)) := by sorry
