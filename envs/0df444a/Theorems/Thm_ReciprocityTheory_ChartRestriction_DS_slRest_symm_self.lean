-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_slRest_symm_self
-- name    : ReciprocityTheory.ChartRestriction.DS.slRest_symm_self
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:12:48.65357+00:00
-- url     : https://prove2.me/theorems/4675caf9-5978-49ef-9f92-f3ea542db456
-- title:
--   DS: sl Rest symm self
-- statement:
--   The DS construction uses the sl Rest symm self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/SltEqZeroOfCompact.lean#L23-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/SltEqZeroOfCompact.lean#L23-L25

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_NcVOneDecomp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_SltEqZeroOfCompact
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
  {E : Fin n → Fin n → Module.End ℂ M}

theorem ReciprocityTheory.ChartRestriction.DS.slRest_symm_self {k : ℕ} (i : Fin k) (p : Fin n × Fin n) (r : {j // j ≠ i} → Fin n × Fin n) :
    (slRest i).symm (p, r) i = p := by sorry
