-- Prove2me | Theorems.Thm_PI_SelfDualLoc_W_hform_map
-- name    : PI.SelfDualLoc.W.hform_map
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T13:47:36.635078+00:00
-- url     : https://prove2.me/theorems/85056672-df4d-460c-9959-2eb080371986
-- title:
--   W: hform map
-- statement:
--   The W construction uses the hform map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SelfDualLocalBasis/HformSumRight.lean#L59-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SelfDualLocalBasis/HformSumRight.lean#L59-L62

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

theorem PI.SelfDualLoc.W.hform_map {B : Type} [CommRing B] (τ : B →+* B) (f : A →+* B)
    (hf : ∀ a, f (σ a) = τ (f a)) (x y : n → A) :
    hform τ (J.map f) (fun i => f (x i)) (fun i => f (y i)) = f (hform σ J x y) := by sorry
