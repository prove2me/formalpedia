-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_DB_U_inv_mul
-- name    : PI.UnitaryGroupMassFormula.UsCost.DB.U_inv_mul
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T16:07:39.402546+00:00
-- url     : https://prove2.me/theorems/cce3a036-aed1-4721-8806-735cbf9f4ed9
-- title:
--   DB: U inv mul
-- statement:
--   The DB construction uses the U inv mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCost/DerivB.lean#L116-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCost/DerivB.lean#L116-L121

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

theorem PI.UnitaryGroupMassFormula.UsCost.DB.U_inv_mul {p s : ℕ} (b : Fin p → Fin s → ℂ) :
    (blk2 (1 : Matrix (Fin p) (Fin p) ℂ) (Matrix.of b) 0 (1 : Matrix (Fin s) (Fin s) ℂ))⁻¹ *
      blk2 1 (Matrix.of b) 0 1 = 1 := by sorry
