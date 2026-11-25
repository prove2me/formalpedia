-- Prove2me | Theorems.Thm_ReciprocityTheory_Cheb_isDiscrete_exp_fiber
-- name    : ReciprocityTheory.Cheb.isDiscrete_exp_fiber
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T10:48:05.609058+00:00
-- url     : https://prove2.me/theorems/e35ef52c-9677-5a2a-8942-1278b4db20b5
-- title:
--   Cheb: is Discrete exp fiber
-- statement:
--   The Cheb construction uses the is Discrete exp fiber property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/NoWind.lean#L7-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/NoWind.lean#L7-L29

import Mathlib
import Definitions.Def_ReciprocityTheory_Chebotarev_NoWind
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Cheb
open Filter Topology Set Complex

theorem ReciprocityTheory.Cheb.isDiscrete_exp_fiber (c : ℂ) : IsDiscrete {w : ℂ | Complex.exp w = c} := by sorry
