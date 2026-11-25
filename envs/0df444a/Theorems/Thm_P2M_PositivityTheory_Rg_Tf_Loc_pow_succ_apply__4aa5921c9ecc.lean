-- Prove2me | Theorems.Thm_P2M_PositivityTheory_Rg_Tf_Loc_pow_succ_apply__4aa5921c9ecc
-- name    : P2M_PositivityTheory_Rg_Tf_Loc_pow_succ_apply__4aa5921c9ecc
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:11:08.274731+00:00
-- url     : https://prove2.me/theorems/e85d91fd-2504-42c4-ae46-7377f2b70a87
-- title:
--   P2 M Positivity Theory Rg Tf Loc pow succ apply  4aa5921c9ecc: P2 M Positivity Theory Rg Tf Loc pow succ apply  4aa5921c9ecc
-- statement:
--   The P2 M Positivity Theory Rg Tf Loc pow succ apply  4aa5921c9ecc construction uses the P2 M Positivity Theory Rg Tf Loc pow succ apply  4aa5921c9ecc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/TwistedFactors/IntegralUnitBaseChange/InvTransposeGLInvTransposeGL.lean#L32-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/TwistedFactors/IntegralUnitBaseChange/InvTransposeGLInvTransposeGL.lean#L32-L34

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_TwistedFactors_IntegralUnitBaseChange_InvTransposeGLInvTransposeGL
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Polynomial
open scoped ENNReal
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Tf PositivityTheory.Rg.Tf.Loc
noncomputable section
variable {G : Type*} [Group G]

theorem P2M_PositivityTheory_Rg_Tf_Loc_pow_succ_apply__4aa5921c9ecc (θ : Monoid.End G) (m : ℕ) (g : G) :
    (θ ^ (m + 1)) g = θ ((θ ^ m) g) := by sorry

alias «PositivityTheory».«Rg».«Tf».«Loc».«pow_succ_apply'» := P2M_PositivityTheory_Rg_Tf_Loc_pow_succ_apply__4aa5921c9ecc
