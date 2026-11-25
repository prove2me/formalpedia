-- Prove2me | Theorems.Thm_ReciprocityTheory_Cheb_restrictNormal_pow_of_gal
-- name    : ReciprocityTheory.Cheb.restrictNormal_pow_of_gal
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T10:48:16.757809+00:00
-- url     : https://prove2.me/theorems/5aec2667-07cd-5c7b-bb9a-ea2e2700d3f7
-- title:
--   Cheb: restrict Normal pow of gal
-- statement:
--   The Cheb construction uses the restrict Normal pow of gal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/CrossFix.lean#L44-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/CrossFix.lean#L44-L46

import Mathlib
import Definitions.Def_ReciprocityTheory_Chebotarev_CrossFix
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
variable {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
    [IsGalois ℚ K] [IsGalois ℚ M]

theorem ReciprocityTheory.Cheb.restrictNormal_pow_of_gal (g : Gal(M/ℚ)) (m : ℕ) :
    AlgEquiv.restrictNormal (g ^ m) K = (AlgEquiv.restrictNormal g K) ^ m := by sorry
