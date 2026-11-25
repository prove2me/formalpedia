-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_DB_sum_dirZ
-- name    : PI.UnitaryGroupMassFormula.UsCost.DB.sum_dirZ
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T06:04:32.459449+00:00
-- url     : https://prove2.me/theorems/c314d2a4-b83a-4a09-abfa-bf221ffc0e62
-- title:
--   DB: sum dir Z
-- statement:
--   The DB construction uses the sum dir Z property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCost/DerivB.lean#L81-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCost/DerivB.lean#L81-L87

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

theorem PI.UnitaryGroupMassFormula.UsCost.DB.sum_dirZ {k p s ρ : ℕ} {σ : Equiv.Perm (Fin p)} (ξ : Xi k p s ρ σ) (Z W : G.Mat s) :
    ∑ i : Fin s × Fin s × Bool, coefZ Z W i • dirZ k ρ ξ i = lamZ k ρ ξ ((Matrix.of Z)⁻¹ * Matrix.of W) := by sorry
