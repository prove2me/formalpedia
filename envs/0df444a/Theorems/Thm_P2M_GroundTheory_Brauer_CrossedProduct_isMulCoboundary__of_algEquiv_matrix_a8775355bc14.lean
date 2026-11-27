-- Prove2me | Theorems.Thm_P2M_GroundTheory_Brauer_CrossedProduct_isMulCoboundary__of_algEquiv_matrix_a8775355bc14
-- name    : P2M_GroundTheory_Brauer_CrossedProduct_isMulCoboundary__of_algEquiv_matrix_a8775355bc14
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T13:08:35.758614+00:00
-- url     : https://prove2.me/theorems/4a327974-ffb8-4403-80bf-2c6fa26d5e15
-- title:
--   P2 M Ground Theory Brauer Crossed Product is Mul Coboundary  of alg Equiv matrix a8775355bc14: P2 M Ground Theory Brauer Crossed Product is Mul Coboundary  of alg Equiv matrix a8775355bc14
-- statement:
--   The P2 M Ground Theory Brauer Crossed Product is Mul Coboundary  of alg Equiv matrix a8775355bc14 construction uses the P2 M Ground Theory Brauer Crossed Product is Mul Coboundary  of alg Equiv matrix a8775355bc14 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/CrossedProductInj.lean#L76-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/CrossedProductInj.lean#L76-L85

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

theorem P2M_GroundTheory_Brauer_CrossedProduct_isMulCoboundary__of_algEquiv_matrix_a8775355bc14 {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hf : IsMulCocycle₂ f) (e : CrossedProduct hf ≃ₐ[K] Matrix ι ι K) : IsMulCoboundary₂ f := by sorry

alias «GroundTheory».«Brauer».«CrossedProduct».«isMulCoboundary₂_of_algEquiv_matrix» := P2M_GroundTheory_Brauer_CrossedProduct_isMulCoboundary__of_algEquiv_matrix_a8775355bc14
