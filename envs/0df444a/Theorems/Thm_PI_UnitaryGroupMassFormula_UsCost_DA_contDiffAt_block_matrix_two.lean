-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_DA_contDiffAt_block_matrix_two
-- name    : PI.UnitaryGroupMassFormula.UsCost.DA.contDiffAt_block_matrix_two
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T06:05:16.725038+00:00
-- url     : https://prove2.me/theorems/75280b50-f97e-4761-a1f9-b25f50b3db9e
-- title:
--   DA: cont Diff At block matrix two
-- statement:
--   The DA construction uses the cont Diff At block matrix two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCost/DerivA.lean#L60-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCost/DerivA.lean#L60-L72

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_LetterSize
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DirectionsInParabolic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_DerivA
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
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UsCost PI.UnitaryGroupMassFormula.UsCost.DA
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {n : WithTop ℕ∞} {x : X}

theorem PI.UnitaryGroupMassFormula.UsCost.DA.contDiffAt_block_matrix_two {p s : ℕ} {A : X → Matrix (Fin p) (Fin p) ℂ} {B' : X → Matrix (Fin p) (Fin s) ℂ}
    {C : X → Matrix (Fin s) (Fin p) ℂ} {D : X → Matrix (Fin s) (Fin s) ℂ}
    (hA : ContDiffAt ℝ n A x) (hB : ContDiffAt ℝ n B' x) (hC : ContDiffAt ℝ n C x) (hD : ContDiffAt ℝ n D x) :
    ContDiffAt ℝ n (fun y => blk2 (A y) (B' y) (C y) (D y)) x := by sorry
