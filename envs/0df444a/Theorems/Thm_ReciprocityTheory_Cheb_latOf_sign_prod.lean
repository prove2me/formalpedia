-- Prove2me | Theorems.Thm_ReciprocityTheory_Cheb_latOf_sign_prod
-- name    : ReciprocityTheory.Cheb.latOf_sign_prod
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T10:49:32.622008+00:00
-- url     : https://prove2.me/theorems/f01048ef-3e7e-5721-8ccb-75c38ce2dafe
-- title:
--   Cheb: lat Of sign prod
-- statement:
--   The Cheb construction uses the lat Of sign prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/DiscreteTopologyLatOf.lean#L74-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/DiscreteTopologyLatOf.lean#L74-L76

import Definitions.Def_ReciprocityTheory_Chebotarev_Ucoord
import Definitions.Def_ReciprocityTheory_Chebotarev_DiscreteTopologyLatOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField NumberField.mixedEmbedding NumberField.Units
open scoped Classical
open ReciprocityTheory ReciprocityTheory.Cheb
variable {E : Type} [Field E] [NumberField E]
open NumberField.InfinitePlace

theorem ReciprocityTheory.Cheb.latOf_sign_prod {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    SignType.sign (∏ i ∈ s, f i) = ∏ i ∈ s, SignType.sign (f i) := by sorry
