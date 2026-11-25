-- Prove2me | Theorems.Thm_P2M_GroundTheory_Brauer_CrossedProduct_isMulCoboundary__div_of_algEquiv_eec8390b77bb
-- name    : P2M_GroundTheory_Brauer_CrossedProduct_isMulCoboundary__div_of_algEquiv_eec8390b77bb
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T06:11:39.323611+00:00
-- url     : https://prove2.me/theorems/36f9cbbc-36e9-55e8-8466-f0d42a47b962
-- title:
--   P2 M Ground Theory Brauer Crossed Product is Mul Coboundary  div of alg Equiv eec8390b77bb: P2 M Ground Theory Brauer Crossed Product is Mul Coboundary  div of alg Equiv eec8390b77bb
-- statement:
--   The P2 M Ground Theory Brauer Crossed Product is Mul Coboundary  div of alg Equiv eec8390b77bb construction uses the P2 M Ground Theory Brauer Crossed Product is Mul Coboundary  div of alg Equiv eec8390b77bb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/CrossedProductInj.lean#L41-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/CrossedProductInj.lean#L41-L74

import Mathlib
import Definitions.Def_GroundTheory_Brauer_CrossedProduct
import Definitions.Def_GroundTheory_Brauer_CrossedProductSimple
import Definitions.Def_GroundTheory_Brauer_CrossedProductMaps
import Definitions.Def_GroundTheory_Brauer_SkolemNoether
import Definitions.Def_GroundTheory_Brauer_IsBrauerEquivalentIffNonemptyAlgEquiv
import Definitions.Def_GroundTheory_Brauer_MulDistribMulActionQuotientFixedPoints
import Definitions.Def_GroundTheory_Brauer_CrossedProductInj
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
open groupCohomology
universe u v
open GroundTheory.Brauer.CrossedProduct
variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable {f : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ} {hf : IsMulCocycle₂ f}
variable [FiniteDimensional K L] [IsGalois K L]

theorem P2M_GroundTheory_Brauer_CrossedProduct_isMulCoboundary__div_of_algEquiv_eec8390b77bb {g : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ}
    (hf : IsMulCocycle₂ f) (hg : IsMulCocycle₂ g) (e : CrossedProduct hf ≃ₐ[K] CrossedProduct hg) :
    IsMulCoboundary₂ (f / g) := by sorry

alias «GroundTheory».«Brauer».«CrossedProduct».«isMulCoboundary₂_div_of_algEquiv» := P2M_GroundTheory_Brauer_CrossedProduct_isMulCoboundary__div_of_algEquiv_eec8390b77bb
