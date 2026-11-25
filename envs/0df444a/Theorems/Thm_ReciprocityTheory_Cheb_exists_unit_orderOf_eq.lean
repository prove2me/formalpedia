-- Prove2me | Theorems.Thm_ReciprocityTheory_Cheb_exists_unit_orderOf_eq
-- name    : ReciprocityTheory.Cheb.exists_unit_orderOf_eq
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T10:47:56.120992+00:00
-- url     : https://prove2.me/theorems/2bb25238-d128-564e-b968-dd49657bebea
-- title:
--   Cheb: exists unit order Of eq
-- statement:
--   The Cheb construction uses the exists unit order Of eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/ExistsUnitOrderOfEq.lean#L14-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/ExistsUnitOrderOfEq.lean#L14-L17

import Mathlib
import Definitions.Def_ReciprocityTheory_Chebotarev_CycStatement
import Definitions.Def_ReciprocityTheory_Chebotarev_CrossGal
import Definitions.Def_ReciprocityTheory_Chebotarev_CrossLift
import Definitions.Def_ReciprocityTheory_Chebotarev_CrossFix
import Definitions.Def_ReciprocityTheory_Chebotarev_CrossFrobE
import Definitions.Def_ReciprocityTheory_Chebotarev_CrossRes
import Definitions.Def_ReciprocityTheory_Chebotarev_CyclotomicIrreducibleOfForallIsUnramifiedAt
import Definitions.Def_ReciprocityTheory_Chebotarev_ExistsUnitOrderOfEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Polynomial
open ReciprocityTheory ReciprocityTheory.Cheb

theorem ReciprocityTheory.Cheb.exists_unit_orderOf_eq (l : ℕ) [Fact l.Prime] : ∃ τ : (ZMod l)ˣ, orderOf τ = l - 1 := by sorry
