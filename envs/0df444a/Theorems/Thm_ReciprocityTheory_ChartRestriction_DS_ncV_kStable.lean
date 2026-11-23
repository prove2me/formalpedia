-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_ncV_kStable
-- name    : ReciprocityTheory.ChartRestriction.DS.ncV_kStable
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:02:11.345678+00:00
-- url     : https://prove2.me/theorems/13711681-3254-496e-909e-8169c2e85a04
-- title:
--   DS: nc V k Stable
-- statement:
--   The DS construction uses the nc V k Stable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/BigRep.lean#L193-L238
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/BigRep.lean#L193-L238

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_Permute
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_IsKUnitaryOfIsInfUnitary
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_BigRep
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

theorem ReciprocityTheory.ChartRestriction.DS.ncV_kStable (hV : IsKStableSub ε E V) (k : ℕ) :
    IsKStableSub ε (bAct E k) (ncV ε V k) := by sorry
