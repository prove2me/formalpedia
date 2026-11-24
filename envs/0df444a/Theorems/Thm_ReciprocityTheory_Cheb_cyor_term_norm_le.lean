-- Prove2me | Theorems.Thm_ReciprocityTheory_Cheb_cyor_term_norm_le
-- name    : ReciprocityTheory.Cheb.cyor_term_norm_le
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:16:32.438857+00:00
-- url     : https://prove2.me/theorems/7a41ac5f-49fc-43be-af7e-383e80703977
-- title:
--   Cheb: cyor term norm le
-- statement:
--   The Cheb construction uses the cyor term norm le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/CycOrth.lean#L24-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/CycOrth.lean#L24-L29

import Definitions.Def_ReciprocityTheory_Chebotarev_NZIdeal
import Definitions.Def_ReciprocityTheory_Chebotarev_CycOrth
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open ReciprocityTheory ReciprocityTheory.Cheb
variable {E : Type} [Field E] [NumberField E]

theorem ReciprocityTheory.Cheb.cyor_term_norm_le {l : ℕ} (χ : DirichletCharacter ℂ l) (q : Prm E) (s : ℝ) :
    ‖χ ((Nrm q : ℕ) : ZMod l) * ((Nrm q : ℕ) : ℂ) ^ (-(s : ℂ))‖ ≤ ((Nrm q : ℕ) : ℝ) ^ (-s) := by sorry
