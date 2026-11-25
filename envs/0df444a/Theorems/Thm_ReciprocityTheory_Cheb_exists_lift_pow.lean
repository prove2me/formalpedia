-- Prove2me | Theorems.Thm_ReciprocityTheory_Cheb_exists_lift_pow
-- name    : ReciprocityTheory.Cheb.exists_lift_pow
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T10:47:47.201819+00:00
-- url     : https://prove2.me/theorems/62fc817e-3b64-4b68-abaa-6c76f0e8c53e
-- title:
--   Cheb: exists lift pow
-- statement:
--   The Cheb construction uses the exists lift pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/CrossLift.lean#L7-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/CrossLift.lean#L7-L51

import Mathlib
import Definitions.Def_ReciprocityTheory_Chebotarev_CrossLift
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

theorem ReciprocityTheory.Cheb.exists_lift_pow {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
    [IsGalois ℚ K] [IsGalois ℚ M] (l : ℕ) [Fact l.Prime] [IsCyclotomicExtension {l} K M]
    (hirr : Irreducible (cyclotomic l K)) {ζ : M} (hζ : IsPrimitiveRoot ζ l) (σ : Gal(K/ℚ)) (τ : (ZMod l)ˣ) :
    ∃ g : Gal(M/ℚ), AlgEquiv.restrictNormal g K = σ ∧ g ζ = ζ ^ (τ : ZMod l).val := by sorry
