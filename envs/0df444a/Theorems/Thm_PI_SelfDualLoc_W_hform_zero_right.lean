-- Prove2me | Theorems.Thm_PI_SelfDualLoc_W_hform_zero_right
-- name    : PI.SelfDualLoc.W.hform_zero_right
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T20:23:49.76102+00:00
-- url     : https://prove2.me/theorems/7b1c41db-8a7e-40b6-9b79-058e19cc3ba4
-- title:
--   W: hform zero right
-- statement:
--   The W construction uses the hform zero right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SelfDualLocalBasis/HformSumRight.lean#L38-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SelfDualLocalBasis/HformSumRight.lean#L38-L39

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SelfDualLoc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SelfDualLocalBasis_HformSumRight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PI PI.SelfDualLoc PI.SelfDualLoc.W
open PI.SelfDualLoc
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]
  (σ : A →+* A) (J : Matrix n n A)

theorem PI.SelfDualLoc.W.hform_zero_right (x : n → A) : hform σ J x 0 = 0 := by sorry
