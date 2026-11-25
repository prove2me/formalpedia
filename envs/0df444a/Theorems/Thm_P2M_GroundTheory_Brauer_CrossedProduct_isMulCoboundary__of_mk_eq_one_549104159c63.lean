-- Prove2me | Theorems.Thm_P2M_GroundTheory_Brauer_CrossedProduct_isMulCoboundary__of_mk_eq_one_549104159c63
-- name    : P2M_GroundTheory_Brauer_CrossedProduct_isMulCoboundary__of_mk_eq_one_549104159c63
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T07:55:19.569006+00:00
-- url     : https://prove2.me/theorems/17241a15-618b-4060-9c2a-1a60cb8b1e5d
-- title:
--   P2 M Ground Theory Brauer Crossed Product is Mul Coboundary  of mk eq one 549104159c63: P2 M Ground Theory Brauer Crossed Product is Mul Coboundary  of mk eq one 549104159c63
-- statement:
--   The P2 M Ground Theory Brauer Crossed Product is Mul Coboundary  of mk eq one 549104159c63 construction uses the P2 M Ground Theory Brauer Crossed Product is Mul Coboundary  of mk eq one 549104159c63 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/CrossedProductInj.lean#L134-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/CrossedProductInj.lean#L134-L136

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
variable {K L : Type u} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
variable {f : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ}

theorem P2M_GroundTheory_Brauer_CrossedProduct_isMulCoboundary__of_mk_eq_one_549104159c63 (hf : IsMulCocycle₂ f)
    (h : (⟦csaOf K (CrossedProduct hf)⟧ : BrauerGroup.{u, u} K) = 1) : IsMulCoboundary₂ f := by sorry

alias «GroundTheory».«Brauer».«CrossedProduct».«isMulCoboundary₂_of_mk_eq_one» := P2M_GroundTheory_Brauer_CrossedProduct_isMulCoboundary__of_mk_eq_one_549104159c63
