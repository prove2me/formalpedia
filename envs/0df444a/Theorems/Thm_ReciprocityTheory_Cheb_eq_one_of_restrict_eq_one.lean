-- Prove2me | Theorems.Thm_ReciprocityTheory_Cheb_eq_one_of_restrict_eq_one
-- name    : ReciprocityTheory.Cheb.eq_one_of_restrict_eq_one
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T10:48:16.816019+00:00
-- url     : https://prove2.me/theorems/3d7df88d-41cb-4fff-bf3d-1a62eb24b20a
-- title:
--   Cheb: eq one of restrict eq one
-- statement:
--   The Cheb construction uses the eq one of restrict eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/CrossFix.lean#L10-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/CrossFix.lean#L10-L24

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

theorem ReciprocityTheory.Cheb.eq_one_of_restrict_eq_one {l : ℕ} [Fact l.Prime] [IsCyclotomicExtension {l} K M]
    {ζ : M} (hζ : IsPrimitiveRoot ζ l) (h : Gal(M/ℚ)) (hK : AlgEquiv.restrictNormal h K = 1) (h1 : h ζ = ζ) : h = 1 := by sorry
