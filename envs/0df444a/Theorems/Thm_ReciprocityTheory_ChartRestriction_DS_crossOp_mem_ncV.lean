-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_crossOp_mem_ncV
-- name    : ReciprocityTheory.ChartRestriction.DS.crossOp_mem_ncV
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:10:33.490993+00:00
-- url     : https://prove2.me/theorems/dc28c163-6d11-4dee-80bf-c44d23f18f80
-- title:
--   DS: cross Op mem nc V
-- statement:
--   The DS construction uses the cross Op mem nc V property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/BigCas.lean#L259-L311
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/BigCas.lean#L259-L311

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

theorem ReciprocityTheory.ChartRestriction.DS.crossOp_mem_ncV (hV : IsKStableSub ε E V) (k : ℕ) (i : Fin k) {F : Big n k M}
    (hF : F ∈ ncV ε V k) : crossOp ε E k i F ∈ ncV ε V k := by sorry
