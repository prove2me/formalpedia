-- Prove2me | Theorems.Thm_ReciprocityTheory_Cheb_two_le_nrm__ac429c
-- name    : ReciprocityTheory.Cheb.two_le_nrm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:16:58.406682+00:00
-- url     : https://prove2.me/theorems/ac429cb4-17ee-4391-bbe4-71b493f4e9a3
-- title:
--   Cheb: two le nrm
-- statement:
--   The Cheb construction uses the two le nrm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/CycTail.lean#L19-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/CycTail.lean#L19-L24

import Definitions.Def_ReciprocityTheory_Chebotarev_NZIdeal
import Definitions.Def_ReciprocityTheory_Chebotarev_CycTail
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open ReciprocityTheory ReciprocityTheory.Cheb
variable {E : Type} [Field E] [NumberField E]

theorem ReciprocityTheory.Cheb.two_le_nrm (q : Prm E) : 2 ≤ Nrm q := by sorry
