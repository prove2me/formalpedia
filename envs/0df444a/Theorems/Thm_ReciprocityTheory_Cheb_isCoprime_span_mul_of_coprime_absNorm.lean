-- Prove2me | Theorems.Thm_ReciprocityTheory_Cheb_isCoprime_span_mul_of_coprime_absNorm
-- name    : ReciprocityTheory.Cheb.isCoprime_span_mul_of_coprime_absNorm
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T10:48:26.885607+00:00
-- url     : https://prove2.me/theorems/f27547a8-2abf-52a1-91ff-c63eb1682a41
-- title:
--   Cheb: is Coprime span mul of coprime abs Norm
-- statement:
--   The Cheb construction uses the is Coprime span mul of coprime abs Norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/MeanZero.lean#L12-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/MeanZero.lean#L12-L32

import Definitions.Def_ReciprocityTheory_Chebotarev_DiscreteTopologyLatOf
import Definitions.Def_ReciprocityTheory_Chebotarev_NormCongr
import Definitions.Def_ReciprocityTheory_Chebotarev_MeanZero
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

theorem ReciprocityTheory.Cheb.isCoprime_span_mul_of_coprime_absNorm {l : ℕ} (B C : Ideal (𝓞 E))
    (hcop : Nat.Coprime (Ideal.absNorm C) (l * Ideal.absNorm B)) :
    IsCoprime (Ideal.span {((l * Ideal.absNorm B : ℕ) : 𝓞 E)} * B) C := by sorry
