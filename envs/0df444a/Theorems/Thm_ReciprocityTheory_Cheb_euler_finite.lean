-- Prove2me | Theorems.Thm_ReciprocityTheory_Cheb_euler_finite
-- name    : ReciprocityTheory.Cheb.euler_finite
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T10:48:51.525858+00:00
-- url     : https://prove2.me/theorems/084cdc08-a810-4496-80ec-7005fbe8f9b9
-- title:
--   Cheb: euler finite
-- statement:
--   The Cheb construction uses the euler finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/EulerFin.lean#L14-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/EulerFin.lean#L14-L78

import Definitions.Def_ReciprocityTheory_Chebotarev_EulerFac
import Definitions.Def_ReciprocityTheory_Chebotarev_EulerFin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Filter Topology
open ReciprocityTheory ReciprocityTheory.Cheb

theorem ReciprocityTheory.Cheb.euler_finite {E : Type} [Field E] [NumberField E] (f : Ideal (𝓞 E) → ℂ) (hf1 : f 1 = 1)
    (hmul : ∀ a b : Ideal (𝓞 E), f (a * b) = f a * f b)
    (hsum : Summable (fun a : NZIdeal E => ‖f a.1‖)) (hlt : ∀ q : Prm E, ‖f q.asIdeal‖ < 1)
    (S : Finset (Prm E)) :
    HasSum (Set.indicator {a : NZIdeal E | Smooth S a.1} (fun a => f a.1)) (∏ q ∈ S, (1 - f q.asIdeal)⁻¹) := by sorry
