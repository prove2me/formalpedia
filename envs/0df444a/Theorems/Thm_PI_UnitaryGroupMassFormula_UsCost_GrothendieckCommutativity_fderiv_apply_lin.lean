-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_GrothendieckCommutativity_fderiv_apply_lin
-- name    : PI.UnitaryGroupMassFormula.UsCost.GrothendieckCommutativity.fderiv_apply_lin
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T06:04:02.316169+00:00
-- url     : https://prove2.me/theorems/46637838-77d4-4418-a405-5371c3670f61
-- title:
--   Grothendieck Commutativity: fderiv apply lin
-- statement:
--   The Grothendieck Commutativity construction uses the fderiv apply lin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCost/RightRegularActionListDLREqAppend.lean#L21-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCost/RightRegularActionListDLREqAppend.lean#L21-L33

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_LetterSize
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_RightRegularActionListDLREqAppend
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.BetaSesquilinearity
open scoped ContDiff
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UsCost PI.UnitaryGroupMassFormula.UsCost.GrothendieckCommutativity
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
attribute [local instance] PI.UnitaryGroupMassFormula.UsCost.GrothendieckCommutativity.clmNACG
attribute [local instance] PI.UnitaryGroupMassFormula.UsCost.GrothendieckCommutativity.clmNS

theorem PI.UnitaryGroupMassFormula.UsCost.GrothendieckCommutativity.fderiv_apply_lin {f' : B.Mat k r → E} {U : Set (B.Mat k r)} (hU : IsOpen U)
    (hc : ContDiffOn ℝ 2 f' U) {g : B.Mat k r} (hg : g ∈ U) (A : B.Mat k r →L[ℝ] B.Mat k r) :
    DifferentiableAt ℝ (fun y => fderiv ℝ f' y (A y)) g ∧
    ∀ V, fderiv ℝ (fun y => fderiv ℝ f' y (A y)) g V =
      fderiv ℝ f' g (A V) + fderiv ℝ (fderiv ℝ f') g V (A g) := by sorry
