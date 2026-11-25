-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_gaXi_contAt
-- name    : PI.UnitaryGroupMassFormula.UsCost.gaXi_contAt
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T08:36:28.353286+00:00
-- url     : https://prove2.me/theorems/efdd6636-1a99-4140-a6b3-3c34061f53f5
-- title:
--   Us Cost: ga Xi cont At
-- statement:
--   The Us Cost construction uses the ga Xi cont At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCost/ContinuousBlockMatrixThree.lean#L88-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCost/ContinuousBlockMatrixThree.lean#L88-L112

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_LetterSize
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Block3MulBlocks
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_ContinuousBlockMatrixThree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UsCost

theorem PI.UnitaryGroupMassFormula.UsCost.gaXi_contAt (k p s ρ : ℕ) (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ) (hd : ∀ i, d i ≠ 0)
    (ξ : Xi k p s ρ σ) (Z : G.Mat s) (γ : B.Mat k ρ) (hZ : G.detM Z ≠ 0) :
    ContinuousAt (fun Z' : G.Mat s => gaXi k ρ σ d ξ Z' γ) Z := by sorry
