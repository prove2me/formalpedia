-- Prove2me | Theorems.Thm_P2M_GroundTheory_Brauer_isMulCoboundary__pow_card_427b229fa3ef
-- name    : P2M_GroundTheory_Brauer_isMulCoboundary__pow_card_427b229fa3ef
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T09:42:05.142291+00:00
-- url     : https://prove2.me/theorems/17b1e5ac-70c3-4b42-9130-b366c8868099
-- title:
--   P2 M Ground Theory Brauer is Mul Coboundary  pow card 427b229fa3ef: P2 M Ground Theory Brauer is Mul Coboundary  pow card 427b229fa3ef
-- statement:
--   The P2 M Ground Theory Brauer is Mul Coboundary  pow card 427b229fa3ef construction uses the P2 M Ground Theory Brauer is Mul Coboundary  pow card 427b229fa3ef property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/CrossedProductIso.lean#L272-L287
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/CrossedProductIso.lean#L272-L287

import Mathlib
import Definitions.Def_GroundTheory_Brauer_CrossedProduct
import Definitions.Def_GroundTheory_Brauer_CrossedProductSimple
import Definitions.Def_GroundTheory_Brauer_CrossedProductMaps
import Definitions.Def_GroundTheory_Brauer_CrossedProductInj
import Definitions.Def_GroundTheory_Brauer_CrossedProductTensor
import Definitions.Def_GroundTheory_Brauer_SkolemNoether
import Definitions.Def_GroundTheory_Brauer_DoubleCentralizer
import Definitions.Def_GroundTheory_Brauer_Splitting
import Definitions.Def_GroundTheory_Brauer_BaseChange
import Definitions.Def_GroundTheory_Brauer_IsBrauerEquivalentIffNonemptyAlgEquiv
import Definitions.Def_GroundTheory_Brauer_MulDistribMulActionQuotientFixedPoints
import Definitions.Def_GroundTheory_Brauer_CrossedProductIso
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
open TensorProduct Module groupCohomology
universe u

theorem P2M_GroundTheory_Brauer_isMulCoboundary__pow_card_427b229fa3ef {G M : Type*} [Group G] [Fintype G] [CommGroup M]
    [MulDistribMulAction G M] {f : G × G → M} (hf : IsMulCocycle₂ f) :
    IsMulCoboundary₂ (f ^ Fintype.card G) := by sorry

alias «GroundTheory».«Brauer».«isMulCoboundary₂_pow_card» := P2M_GroundTheory_Brauer_isMulCoboundary__pow_card_427b229fa3ef
