-- Prove2me | Theorems.Thm_ReciprocityTheory_Cheb_isArithFrobAt_restrictNormal
-- name    : ReciprocityTheory.Cheb.isArithFrobAt_restrictNormal
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T10:48:01.534702+00:00
-- url     : https://prove2.me/theorems/77138adb-158c-5792-bc4b-dba9d9819fc8
-- title:
--   Cheb: is Arith Frob At restrict Normal
-- statement:
--   The Cheb construction uses the is Arith Frob At restrict Normal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/CrossRes.lean#L7-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/CrossRes.lean#L7-L22

import Mathlib
import Definitions.Def_ReciprocityTheory_Chebotarev_CrossRes
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

theorem ReciprocityTheory.Cheb.isArithFrobAt_restrictNormal {K M : Type} [Field K] [NumberField K] [IsGalois ℚ K] [Field M] [NumberField M]
    [Algebra K M] (g : Gal(M/ℚ)) (p : ℕ) (P : Ideal (𝓞 M)) (hP : P.IsPrime)
    (hPp : P.LiesOver (Ideal.span {(p : ℤ)})) (h : IsArithFrobAt ℤ g P) :
    (P.under (𝓞 K)).IsPrime ∧ (P.under (𝓞 K)).LiesOver (Ideal.span {(p : ℤ)}) ∧
      IsArithFrobAt ℤ (AlgEquiv.restrictNormal g K) (P.under (𝓞 K)) := by sorry
