-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_coord_wt_eq
-- name    : ReciprocityTheory.ChartRestriction.DS.coord_wt_eq
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T09:50:29.945718+00:00
-- url     : https://prove2.me/theorems/617474c6-b5e2-4325-8e60-e0862d006467
-- title:
--   DS: coord wt eq
-- statement:
--   The DS construction uses the coord wt eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/DiscreteSeriesExistence/CFPrimeB.lean#L75-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/DiscreteSeriesExistence/CFPrimeB.lean#L75-L84

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CFPrimeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_LayerWeight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CFPrimeB
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
variable {n : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M]

theorem ReciprocityTheory.ChartRestriction.DS.coord_wt_eq (ε : Fin n → Bool) {ν : Fin n → ℝ} {f : Fock n}
    (hf : ∀ c, sgE ε cpFock cmFock c c f = ((ν c : ℝ) : ℂ) • f) {s : Finset (Fin (n * n))}
    (hs : (fockBasis n).coord s f ≠ 0) : ν = fockWt ε s := by sorry
