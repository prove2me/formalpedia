-- Prove2me | Theorems.Thm_ReciprocityTheory_Cheb_irreducible_cyclotomic_fixedField
-- name    : ReciprocityTheory.Cheb.irreducible_cyclotomic_fixedField
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T10:48:13.221155+00:00
-- url     : https://prove2.me/theorems/090fa2e3-d842-4739-9b4c-2d679ccaef65
-- title:
--   Cheb: irreducible cyclotomic fixed Field
-- statement:
--   The Cheb construction uses the irreducible cyclotomic fixed Field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/CrossFix.lean#L81-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/CrossFix.lean#L81-L134

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

theorem ReciprocityTheory.Cheb.irreducible_cyclotomic_fixedField {l : ℕ} [Fact l.Prime] [IsCyclotomicExtension {l} K M]
    {ζ : M} (hζ : IsPrimitiveRoot ζ l) (σ : Gal(K/ℚ)) (hσ : orderOf σ ∣ l - 1) (τ : (ZMod l)ˣ) (hτ : orderOf τ = l - 1)
    (g : Gal(M/ℚ)) (hg : AlgEquiv.restrictNormal g K = σ) (hgζ : g ζ = ζ ^ (τ : ZMod l).val) :
    Irreducible (cyclotomic l (IntermediateField.fixedField (Subgroup.zpowers g))) := by sorry
