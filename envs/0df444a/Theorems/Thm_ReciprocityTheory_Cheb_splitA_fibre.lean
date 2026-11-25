-- Prove2me | Theorems.Thm_ReciprocityTheory_Cheb_splitA_fibre
-- name    : ReciprocityTheory.Cheb.splitA_fibre
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T10:49:08.367902+00:00
-- url     : https://prove2.me/theorems/f074ddd1-edcd-51ce-b2d8-5d4eb955d33d
-- title:
--   Cheb: split A fibre
-- statement:
--   The Cheb construction uses the split A fibre property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/SplitA.lean#L79-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/SplitA.lean#L79-L103

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

theorem ReciprocityTheory.Cheb.splitA_fibre (E : Type) [Field E] [NumberField E] (l : ℕ) [Fact l.Prime]
    (hirr : Irreducible (Polynomial.cyclotomic l E)) (q : Prm E) :
    {P : Prm (CyclotomicField l E) | under P = q}.Finite ∧
      {P : Prm (CyclotomicField l E) | under P = q}.ncard ≤ l - 1 := by sorry
