-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_crossOp_symm
-- name    : ReciprocityTheory.ChartRestriction.DS.crossOp_symm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:53:04.27916+00:00
-- url     : https://prove2.me/theorems/d835b2ee-76bb-447a-9219-77e8cae21f84
-- title:
--   DS: cross Op symm
-- statement:
--   The DS construction uses the cross Op symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/BigCas.lean#L159-L191
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/BigCas.lean#L159-L191

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

theorem ReciprocityTheory.ChartRestriction.DS.crossOp_symm (hU : IsInfUnitary ε E) (k : ℕ) (i : Fin k) (F G : Big n k M) :
    inner ℂ (crossOp ε E k i F) G = inner ℂ F (crossOp ε E k i G) := by sorry
