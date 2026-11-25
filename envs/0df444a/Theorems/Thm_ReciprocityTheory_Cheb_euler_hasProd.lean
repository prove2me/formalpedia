-- Prove2me | Theorems.Thm_ReciprocityTheory_Cheb_euler_hasProd
-- name    : ReciprocityTheory.Cheb.euler_hasProd
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T10:48:29.092977+00:00
-- url     : https://prove2.me/theorems/1f61c43f-2500-50d3-a53a-1e9ad4ee53d3
-- title:
--   Cheb: euler has Prod
-- statement:
--   The Cheb construction uses the euler has Prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/EulerLim.lean#L14-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/EulerLim.lean#L14-L32

import Definitions.Def_ReciprocityTheory_Chebotarev_EulerFin
import Definitions.Def_ReciprocityTheory_Chebotarev_EulerLim
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

theorem ReciprocityTheory.Cheb.euler_hasProd {E : Type} [Field E] [NumberField E] (f : Ideal (𝓞 E) → ℂ) (hf1 : f 1 = 1)
    (hmul : ∀ a b : Ideal (𝓞 E), f (a * b) = f a * f b)
    (hsum : Summable (fun a : NZIdeal E => ‖f a.1‖)) (hlt : ∀ q : Prm E, ‖f q.asIdeal‖ < 1) :
    HasProd (fun q : Prm E => (1 - f q.asIdeal)⁻¹) (∑' a : NZIdeal E, f a.1) := by sorry
