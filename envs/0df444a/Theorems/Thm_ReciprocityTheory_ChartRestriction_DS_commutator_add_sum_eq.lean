-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_commutator_add_sum_eq
-- name    : ReciprocityTheory.ChartRestriction.DS.commutator_add_sum_eq
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T09:50:20.276186+00:00
-- url     : https://prove2.me/theorems/63946108-9ed3-4620-bffd-b14979fce060
-- title:
--   DS: commutator add sum eq
-- statement:
--   The DS construction uses the commutator add sum eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/BigRep.lean#L27-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/BigRep.lean#L27-L42

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
variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M]

theorem ReciprocityTheory.ChartRestriction.DS.commutator_add_sum_eq {R : Type*} [Ring R] {k : ℕ} (m m' : R) (s s' : Fin k → R)
    (h1 : ∀ j, m * s' j = s' j * m) (h2 : ∀ i, s i * m' = m' * s i)
    (h3 : ∀ i j, i ≠ j → s i * s' j = s' j * s i) :
    (m + ∑ i, s i) * (m' + ∑ j, s' j) - (m' + ∑ j, s' j) * (m + ∑ i, s i) =
      (m * m' - m' * m) + ∑ i, (s i * s' i - s' i * s i) := by sorry
