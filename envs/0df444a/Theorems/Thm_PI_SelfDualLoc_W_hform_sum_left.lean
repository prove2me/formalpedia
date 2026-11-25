-- Prove2me | Theorems.Thm_PI_SelfDualLoc_W_hform_sum_left
-- name    : PI.SelfDualLoc.W.hform_sum_left
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:23:13.26781+00:00
-- url     : https://prove2.me/theorems/11fc5dfd-323e-57c9-9ed1-c6db134b8f04
-- title:
--   W: hform sum left
-- statement:
--   The W construction uses the hform sum left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SelfDualLocalBasis/HformSumRight.lean#L50-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SelfDualLocalBasis/HformSumRight.lean#L50-L57

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

theorem PI.SelfDualLoc.W.hform_sum_left {ι : Type} (s : Finset ι) (f : ι → n → A) (y : n → A) :
    hform σ J (∑ k ∈ s, f k) y = ∑ k ∈ s, hform σ J (f k) y := by sorry
