-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_crossOp_comm
-- name    : ReciprocityTheory.ChartRestriction.DS.crossOp_comm
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T03:02:49.168934+00:00
-- url     : https://prove2.me/theorems/326ceb17-78e4-4f51-99d5-7956a1b28477
-- title:
--   DS: cross Op comm
-- statement:
--   The DS construction uses the cross Op comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/BigCas.lean#L193-L257
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/BigCas.lean#L193-L257

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_BigRep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_BigCasA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_BigCas
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M}

theorem ReciprocityTheory.ChartRestriction.DS.crossOp_comm (hE : IsGlRep E) (k : ℕ) (i : Fin k) {a b : Fin n} (hab : ε a = ε b) :
    crossOp ε E k i * bAct E k a b = bAct E k a b * crossOp ε E k i := by sorry
