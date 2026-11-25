-- Prove2me | Theorems.Thm_P2M_GroundTheory_Brauer_CrossedProduct_isMulCocycle__mul_59f558ca0817
-- name    : P2M_GroundTheory_Brauer_CrossedProduct_isMulCocycle__mul_59f558ca0817
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T13:07:57.777915+00:00
-- url     : https://prove2.me/theorems/1e28206d-e45b-5597-84b1-5da8fa76af97
-- title:
--   P2 M Ground Theory Brauer Crossed Product is Mul Cocycle  mul 59f558ca0817: P2 M Ground Theory Brauer Crossed Product is Mul Cocycle  mul 59f558ca0817
-- statement:
--   The P2 M Ground Theory Brauer Crossed Product is Mul Cocycle  mul 59f558ca0817 construction uses the P2 M Ground Theory Brauer Crossed Product is Mul Cocycle  mul 59f558ca0817 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/CrossedProductTensor.lean#L36-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/CrossedProductTensor.lean#L36-L37

import Mathlib
import Definitions.Def_GroundTheory_Brauer_CrossedProduct
import Definitions.Def_GroundTheory_Brauer_CrossedProductSimple
import Definitions.Def_GroundTheory_Brauer_CrossedProductMaps
import Definitions.Def_GroundTheory_Brauer_CrossedProductRegular
import Definitions.Def_GroundTheory_Brauer_CrossedProductInj
import Definitions.Def_GroundTheory_Brauer_TensorSimple
import Definitions.Def_GroundTheory_Brauer_IsBrauerEquivalentIffNonemptyAlgEquiv
import Definitions.Def_GroundTheory_Brauer_BaseChangeCSA
import Definitions.Def_GroundTheory_Brauer_BaseChange
import Definitions.Def_GroundTheory_Brauer_MulDistribMulActionQuotientFixedPoints
import Definitions.Def_GroundTheory_Brauer_CrossedProductTensor
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
open groupCohomology TensorProduct
universe u
open GroundTheory.Brauer.CrossedProduct
variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  [DecidableEq (L ≃ₐ[K] L)]
variable {f g : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ}
omit [FiniteDimensional K L] [DecidableEq (L ≃ₐ[K] L)]

theorem P2M_GroundTheory_Brauer_CrossedProduct_isMulCocycle__mul_59f558ca0817 (hf : IsMulCocycle₂ f) (hg : IsMulCocycle₂ g) : IsMulCocycle₂ (f * g) := by sorry

alias «GroundTheory».«Brauer».«CrossedProduct».«isMulCocycle₂_mul» := P2M_GroundTheory_Brauer_CrossedProduct_isMulCocycle__mul_59f558ca0817
