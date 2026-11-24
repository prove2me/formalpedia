-- Prove2me | Theorems.Thm_ReciprocityTheory_Cheb_liesOver_of_under_eq
-- name    : ReciprocityTheory.Cheb.liesOver_of_under_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:21:17.617381+00:00
-- url     : https://prove2.me/theorems/85c8f50a-f2c3-4ee0-ac39-0c42babdbbcb
-- title:
--   Cheb: lies Over of under eq
-- statement:
--   The Cheb construction uses the lies Over of under eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/SplitA.lean#L7-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/SplitA.lean#L7-L9

import Definitions.Def_ReciprocityTheory_Chebotarev_SplitDef
import Definitions.Def_ReciprocityTheory_Chebotarev_SplitA
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

theorem ReciprocityTheory.Cheb.liesOver_of_under_eq {E E' : Type} [Field E] [NumberField E] [Field E'] [NumberField E'] [Algebra E E']
    (P : Prm E') (q : Prm E) (hP : under P = q) : P.asIdeal.LiesOver q.asIdeal := by sorry
