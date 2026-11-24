-- Prove2me | Theorems.Thm_ReciprocityTheory_Cheb_under_asIdeal
-- name    : ReciprocityTheory.Cheb.under_asIdeal
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:10:11.440842+00:00
-- url     : https://prove2.me/theorems/38d5d970-2f9a-4a8c-9a79-3bbe93f1f69f
-- title:
--   Cheb: under as Ideal
-- statement:
--   The Cheb construction uses the under as Ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/SplitDef.lean#L13-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/SplitDef.lean#L13-L14

import Definitions.Def_ReciprocityTheory_Chebotarev_NZIdeal
import Definitions.Def_ReciprocityTheory_Chebotarev_SplitDef
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

theorem ReciprocityTheory.Cheb.under_asIdeal {E E' : Type} [Field E] [NumberField E] [Field E'] [NumberField E'] [Algebra E E']
    (P : Prm E') : (under (E := E) P).asIdeal = P.asIdeal.under (𝓞 E) := by sorry
