-- Prove2me | Theorems.Thm_ReciprocityTheory_Cheb_smooth_empty_iff
-- name    : ReciprocityTheory.Cheb.smooth_empty_iff
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T10:49:23.776795+00:00
-- url     : https://prove2.me/theorems/e10f2451-0daf-5e63-8f15-4fd10013f378
-- title:
--   Cheb: smooth empty iff
-- statement:
--   The Cheb construction uses the smooth empty iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/EulerFac.lean#L14-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/EulerFac.lean#L14-L25

import Definitions.Def_ReciprocityTheory_Chebotarev_NZIdeal
import Definitions.Def_ReciprocityTheory_Chebotarev_EulerFac
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Filter Topology
open ReciprocityTheory ReciprocityTheory.Cheb

theorem ReciprocityTheory.Cheb.smooth_empty_iff {E : Type} [Field E] [NumberField E] {a : Ideal (𝓞 E)} (ha : a ≠ ⊥) :
    Smooth ∅ a ↔ a = ⊤ := by sorry
