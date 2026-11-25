-- Prove2me | Theorems.Thm_ReciprocityTheory_Cheb_tsum_gfun
-- name    : ReciprocityTheory.Cheb.tsum_gfun
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:51:03.974058+00:00
-- url     : https://prove2.me/theorems/d3eed471-3ae5-5134-bdee-dc2f8ac5768a
-- title:
--   Cheb: tsum gfun
-- statement:
--   The Cheb construction uses the tsum gfun property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/SummableGfun.lean#L21-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/SummableGfun.lean#L21-L41

import Definitions.Def_ReciprocityTheory_Chebotarev_KHoldA
import Definitions.Def_ReciprocityTheory_Chebotarev_CTrick
import Definitions.Def_ReciprocityTheory_Chebotarev_PowerSeriesDiagonalLinear
import Definitions.Def_ReciprocityTheory_Chebotarev_SummableGfun
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField NumberField.Units Filter Topology Set
open scoped Classical
open ReciprocityTheory ReciprocityTheory.Cheb

theorem ReciprocityTheory.Cheb.tsum_gfun {E : Type} [Field E] [NumberField E] {l : ℕ} (χ : DirichletCharacter ℂ l)
    (c : NZIdeal E) {s : ℝ} (hs : 1 < s) :
    ∑' a, gfun χ c s a = Lser E χ s * (1 - (Ideal.absNorm c.1 : ℂ) *
      (χ ((Ideal.absNorm c.1 : ℕ) : ZMod l) * ((Ideal.absNorm c.1 : ℕ) : ℂ) ^ (-(s : ℂ)))) := by sorry
