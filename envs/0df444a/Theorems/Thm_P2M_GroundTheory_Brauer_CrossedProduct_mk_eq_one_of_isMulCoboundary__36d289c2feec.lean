-- Prove2me | Theorems.Thm_P2M_GroundTheory_Brauer_CrossedProduct_mk_eq_one_of_isMulCoboundary__36d289c2feec
-- name    : P2M_GroundTheory_Brauer_CrossedProduct_mk_eq_one_of_isMulCoboundary__36d289c2feec
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T07:53:39.680199+00:00
-- url     : https://prove2.me/theorems/999d7497-7a49-4940-9658-3d7512e6404c
-- title:
--   P2 M Ground Theory Brauer Crossed Product mk eq one of is Mul Coboundary  36d289c2feec: P2 M Ground Theory Brauer Crossed Product mk eq one of is Mul Coboundary  36d289c2feec
-- statement:
--   The P2 M Ground Theory Brauer Crossed Product mk eq one of is Mul Coboundary  36d289c2feec construction uses the P2 M Ground Theory Brauer Crossed Product mk eq one of is Mul Coboundary  36d289c2feec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/CrossedProductInj.lean#L138-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/CrossedProductInj.lean#L138-L146

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

theorem P2M_GroundTheory_Brauer_CrossedProduct_mk_eq_one_of_isMulCoboundary__36d289c2feec (hf : IsMulCocycle₂ f) (h : IsMulCoboundary₂ f) :
    (⟦csaOf K (CrossedProduct hf)⟧ : BrauerGroup.{u, u} K) = 1 := by sorry

alias «GroundTheory».«Brauer».«CrossedProduct».«mk_eq_one_of_isMulCoboundary₂» := P2M_GroundTheory_Brauer_CrossedProduct_mk_eq_one_of_isMulCoboundary__36d289c2feec
