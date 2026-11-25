-- Prove2me | Theorems.Thm_ReciprocityTheory_Cheb_psum_term_norm_le
-- name    : ReciprocityTheory.Cheb.psum_term_norm_le
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T10:48:26.430709+00:00
-- url     : https://prove2.me/theorems/e94feaee-25eb-4e79-bfff-856047371840
-- title:
--   Cheb: psum term norm le
-- statement:
--   The Cheb construction uses the psum term norm le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/PrimeSum.lean#L21-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/PrimeSum.lean#L21-L29

import Definitions.Def_ReciprocityTheory_Chebotarev_CasimirPowerSurjectiveSymmetric
import Definitions.Def_ReciprocityTheory_Chebotarev_EulerSum
import Definitions.Def_ReciprocityTheory_Chebotarev_PrimeSum
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

theorem ReciprocityTheory.Cheb.psum_term_norm_le {E : Type} [Field E] [NumberField E] {l : ℕ} (χ : DirichletCharacter ℂ l) (s : ℝ)
    (q : Prm E) :
    ‖χ ((Nrm q : ℕ) : ZMod l) * ((Nrm q : ℕ) : ℂ) ^ (-(s : ℂ))‖ ≤ ((Nrm q : ℕ) : ℝ) ^ (-s) := by sorry
