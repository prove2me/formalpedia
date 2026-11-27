-- Prove2me | Theorems.Thm_P2M_GroundTheory_Brauer_CrossedProduct_exists_algEquiv_of_isMulCoboundary__ca4eaaf3483d
-- name    : P2M_GroundTheory_Brauer_CrossedProduct_exists_algEquiv_of_isMulCoboundary__ca4eaaf3483d
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T13:08:40.608636+00:00
-- url     : https://prove2.me/theorems/0bb2537c-26cc-40a1-ba16-0ae2fb434211
-- title:
--   P2 M Ground Theory Brauer Crossed Product exists alg Equiv of is Mul Coboundary  ca4eaaf3483d: P2 M Ground Theory Brauer Crossed Product exists alg Equiv of is Mul Coboundary  ca4eaaf3483d
-- statement:
--   The P2 M Ground Theory Brauer Crossed Product exists alg Equiv of is Mul Coboundary  ca4eaaf3483d construction uses the P2 M Ground Theory Brauer Crossed Product exists alg Equiv of is Mul Coboundary  ca4eaaf3483d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/CrossedProductMaps.lean#L152-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/CrossedProductMaps.lean#L152-L155

import Mathlib
import Definitions.Def_GroundTheory_Brauer_CrossedProduct
import Definitions.Def_GroundTheory_Brauer_CrossedProductSimple
import Definitions.Def_GroundTheory_Brauer_CrossedProductMaps
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Brauer
open GroundTheory.Brauer.CrossedProduct
open groupCohomology
variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable {f : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ} {hf : IsMulCocycle₂ f}
variable {f' : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ}

theorem P2M_GroundTheory_Brauer_CrossedProduct_exists_algEquiv_of_isMulCoboundary__ca4eaaf3483d (hf : IsMulCocycle₂ f) (hf' : IsMulCocycle₂ f')
    (h : IsMulCoboundary₂ (f' / f)) :
    ∃ e : CrossedProduct hf ≃ₐ[K] CrossedProduct hf', ∀ a : L, e (incl a) = incl a := by sorry

alias «GroundTheory».«Brauer».«CrossedProduct».«exists_algEquiv_of_isMulCoboundary₂» := P2M_GroundTheory_Brauer_CrossedProduct_exists_algEquiv_of_isMulCoboundary__ca4eaaf3483d
