-- Prove2me | Theorems.Thm_ReciprocityTheory_Cheb_isGalois_cyclotomicField
-- name    : ReciprocityTheory.Cheb.isGalois_cyclotomicField
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T10:48:20.686334+00:00
-- url     : https://prove2.me/theorems/6465eda7-5129-46cf-a6c5-84942c27c771
-- title:
--   Cheb: is Galois cyclotomic Field
-- statement:
--   The Cheb construction uses the is Galois cyclotomic Field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/CrossGal.lean#L21-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/CrossGal.lean#L21-L30

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

theorem ReciprocityTheory.Cheb.isGalois_cyclotomicField (K : Type) [Field K] [NumberField K] [IsGalois ℚ K] (l : ℕ) [NeZero l] :
    IsGalois ℚ (CyclotomicField l K) := by sorry
