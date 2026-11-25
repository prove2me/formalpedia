-- Prove2me | Theorems.Thm_ReciprocityTheory_Cheb_tsum_class_eq_latSum
-- name    : ReciprocityTheory.Cheb.tsum_class_eq_latSum
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:49:08.410795+00:00
-- url     : https://prove2.me/theorems/cf5b08e1-3c69-4700-a891-6a949d01c0eb
-- title:
--   Cheb: tsum class eq lat Sum
-- statement:
--   The Cheb construction uses the tsum class eq lat Sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/IdealLat.lean#L33-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/IdealLat.lean#L33-L114

import Definitions.Def_ReciprocityTheory_Chebotarev_UnitPart
import Definitions.Def_ReciprocityTheory_Chebotarev_DiscreteTopologyLatOf
import Definitions.Def_ReciprocityTheory_Chebotarev_IdealLat
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

theorem ReciprocityTheory.Cheb.tsum_class_eq_latSum (b : NZIdeal E) (H : Ideal (𝓞 E) → ℂ)
    (hH : Summable fun a : NZIdeal E => H (a.1 * b.1)) :
    ∑' a : NZIdeal E, (if cls a * cls b = 1 then H (a.1 * b.1) else 0) =
      ((torsionOrder E : ℕ) : ℂ)⁻¹ *
        ∑' α : b.1, ((uphi (embZ (α : 𝓞 E)) : ℝ) : ℂ) * H (Ideal.span {(α : 𝓞 E)}) := by sorry
