-- Prove2me | Theorems.Thm_ReciprocityTheory_Cheb_splitA_finite_not_coprime
-- name    : ReciprocityTheory.Cheb.splitA_finite_not_coprime
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:21:54.023013+00:00
-- url     : https://prove2.me/theorems/6eba6518-3b4c-4ee9-ba43-44264a64967b
-- title:
--   Cheb: split A finite not coprime
-- statement:
--   The Cheb construction uses the split A finite not coprime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/SplitA.lean#L128-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/SplitA.lean#L128-L134

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

theorem ReciprocityTheory.Cheb.splitA_finite_not_coprime (E : Type) [Field E] [NumberField E] (n : ℕ) (hn : n ≠ 0) :
    {q : Prm E | ¬ Nat.Coprime (Nrm q) n}.Finite := by sorry
