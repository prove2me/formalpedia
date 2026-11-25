-- Prove2me | Theorems.Thm_ReciprocityTheory_Cheb_pow_apply_zeta_of_apply_eq_pow
-- name    : ReciprocityTheory.Cheb.pow_apply_zeta_of_apply_eq_pow
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T10:48:01.26947+00:00
-- url     : https://prove2.me/theorems/579a39c1-715d-50b2-9008-e09083af4b7c
-- title:
--   Cheb: pow apply zeta of apply eq pow
-- statement:
--   The Cheb construction uses the pow apply zeta of apply eq pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/CrossFix.lean#L26-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/CrossFix.lean#L26-L30

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

theorem ReciprocityTheory.Cheb.pow_apply_zeta_of_apply_eq_pow {ζ : M} (g : Gal(M/ℚ)) (t : ℕ) (hg : g ζ = ζ ^ t) (m : ℕ) :
    (g ^ m) ζ = ζ ^ (t ^ m) := by sorry
