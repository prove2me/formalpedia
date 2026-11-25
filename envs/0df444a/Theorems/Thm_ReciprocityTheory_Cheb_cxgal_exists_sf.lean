-- Prove2me | Theorems.Thm_ReciprocityTheory_Cheb_cxgal_exists_sf
-- name    : ReciprocityTheory.Cheb.cxgal_exists_sf
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T10:47:42.190801+00:00
-- url     : https://prove2.me/theorems/c54daed9-7172-58f4-9ebc-4a5d83ffb7f4
-- title:
--   Cheb: cxgal exists sf
-- statement:
--   The Cheb construction uses the cxgal exists sf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/CrossGal.lean#L7-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/CrossGal.lean#L7-L19

import Mathlib
import Definitions.Def_ReciprocityTheory_Chebotarev_CrossGal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Polynomial
open ReciprocityTheory ReciprocityTheory.Cheb

theorem ReciprocityTheory.Cheb.cxgal_exists_sf (K : Type) [Field K] [NumberField K] [IsGalois ℚ K] :
    ∃ p : ℚ[X], p ≠ 0 ∧ IsSplittingField ℚ K p := by sorry
