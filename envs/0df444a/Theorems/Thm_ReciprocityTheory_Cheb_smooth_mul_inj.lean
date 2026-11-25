-- Prove2me | Theorems.Thm_ReciprocityTheory_Cheb_smooth_mul_inj
-- name    : ReciprocityTheory.Cheb.smooth_mul_inj
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T10:49:58.640495+00:00
-- url     : https://prove2.me/theorems/c504dce2-0c6e-50ca-a69d-7d0b82f43e26
-- title:
--   Cheb: smooth mul inj
-- statement:
--   The Cheb construction uses the smooth mul inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/EulerFac.lean#L47-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/EulerFac.lean#L47-L62

import Definitions.Def_ReciprocityTheory_Chebotarev_NZIdeal
import Definitions.Def_ReciprocityTheory_Chebotarev_EulerFac
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

theorem ReciprocityTheory.Cheb.smooth_mul_inj {E : Type} [Field E] [NumberField E] {S : Finset (Prm E)} {q : Prm E} (hq : q ∉ S)
    {b b' : Ideal (𝓞 E)} (hb : Smooth S b) (hb' : Smooth S b') {k k' : ℕ}
    (h : q.asIdeal ^ k * b = q.asIdeal ^ k' * b') : k = k' ∧ b = b' := by sorry
