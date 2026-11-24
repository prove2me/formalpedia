-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_DB_phi_rep
-- name    : PI.UnitaryGroupMassFormula.UsCost.DB.phi_rep
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T16:06:42.633148+00:00
-- url     : https://prove2.me/theorems/8e0ed863-ebe8-4809-8406-c20c8fdbd555
-- title:
--   DB: phi rep
-- statement:
--   The DB construction uses the phi rep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCost/DerivB.lean#L106-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCost/DerivB.lean#L106-L114

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_DerivA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Block3MulBlocks
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_DerivB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UsCost PI.UnitaryGroupMassFormula.UsCost.DB
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open PI.UnitaryGroupMassFormula.UsCost PI.UnitaryGroupMassFormula.UsCost.DA
variable {k p s ρ : ℕ} {σ : Equiv.Perm (Fin p)} {d : Fin p → ℂ}

theorem PI.UnitaryGroupMassFormula.UsCost.DB.phi_rep (hSZ : SliceZ) (ξ : Xi k p s ρ σ) {Z : G.Mat s} (hZ : G.detM Z ≠ 0) (γ : B.Mat k ρ) (Z' : G.Mat s) :
    gaXi k ρ σ d ξ Z' γ = gaXi k ρ σ d ξ Z γ * ((Rn k (p + s) ρ ξ.1.2)⁻¹ *
      muP k (p + s) ρ ((blk2 1 (Matrix.of ξ.2.1.2) 0 1)⁻¹ *
        blk2 1 0 0 ((Matrix.of Z)⁻¹ * Matrix.of Z') * blk2 1 (Matrix.of ξ.2.1.2) 0 1) *
      Rn k (p + s) ρ ξ.1.2) := by sorry
