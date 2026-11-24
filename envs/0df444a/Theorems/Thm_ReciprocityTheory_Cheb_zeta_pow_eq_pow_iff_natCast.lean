-- Prove2me | Theorems.Thm_ReciprocityTheory_Cheb_zeta_pow_eq_pow_iff_natCast
-- name    : ReciprocityTheory.Cheb.zeta_pow_eq_pow_iff_natCast
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:22:01.53983+00:00
-- url     : https://prove2.me/theorems/761c6bc0-6abc-44a5-86d6-2763a0429b61
-- title:
--   Cheb: zeta pow eq pow iff nat Cast
-- statement:
--   The Cheb construction uses the zeta pow eq pow iff nat Cast property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/CrossFix.lean#L32-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/CrossFix.lean#L32-L36

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

theorem ReciprocityTheory.Cheb.zeta_pow_eq_pow_iff_natCast {l : ℕ} [NeZero l] {ζ : M} (hζ : IsPrimitiveRoot ζ l) (a b : ℕ) :
    ζ ^ a = ζ ^ b ↔ (a : ZMod l) = b := by sorry
