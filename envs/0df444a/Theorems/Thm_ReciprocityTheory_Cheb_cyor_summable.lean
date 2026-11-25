-- Prove2me | Theorems.Thm_ReciprocityTheory_Cheb_cyor_summable
-- name    : ReciprocityTheory.Cheb.cyor_summable
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:11:58.549599+00:00
-- url     : https://prove2.me/theorems/20fba970-9062-4b9e-83e3-85f3940ba6d5
-- title:
--   Cheb: cyor summable
-- statement:
--   The Cheb construction uses the cyor summable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/CycOrth.lean#L31-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/CycOrth.lean#L31-L34

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

theorem ReciprocityTheory.Cheb.cyor_summable {l : ℕ} (χ : DirichletCharacter ℂ l) (s : ℝ)
    (hS : Summable (fun q : Prm E => ((Nrm q : ℕ) : ℝ) ^ (-s))) :
    Summable (fun q : Prm E => χ ((Nrm q : ℕ) : ZMod l) * ((Nrm q : ℕ) : ℂ) ^ (-(s : ℂ))) := by sorry
