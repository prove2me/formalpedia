-- Prove2me | Theorems.Thm_PI_SelfDualLoc_W_hform_sum_right
-- name    : PI.SelfDualLoc.W.hform_sum_right
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T13:47:51.929938+00:00
-- url     : https://prove2.me/theorems/202fcba8-6ed4-4a78-a9c7-aec0abb4a8b2
-- title:
--   W: hform sum right
-- statement:
--   The W construction uses the hform sum right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SelfDualLocalBasis/HformSumRight.lean#L41-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SelfDualLocalBasis/HformSumRight.lean#L41-L48

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

theorem PI.SelfDualLoc.W.hform_sum_right {ι : Type} (s : Finset ι) (x : n → A) (f : ι → n → A) :
    hform σ J x (∑ k ∈ s, f k) = ∑ k ∈ s, hform σ J x (f k) := by sorry
