-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_lam_hol
-- name    : ReciprocityTheory.ChartRestriction.DS.S7.lam_hol
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:32:21.084914+00:00
-- url     : https://prove2.me/theorems/7d6bb768-7f8d-4be7-9a4a-4c1e01d82a59
-- title:
--   S7: lam hol
-- statement:
--   The S7 construction uses the lam hol property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/SmulOneMemUnitary.lean#L188-L262
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/SmulOneMemUnitary.lean#L188-L262

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_InhabA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_SmulOneMemUnitary
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}

theorem ReciprocityTheory.ChartRestriction.DS.S7.lam_hol (p q : ℕ) (a b : ℤ) (i : Fin (p + q)) :
    (detWt p q a b - rhoN (epsHol p q) + rhoC (epsHol p q)) i =
      if (i : ℕ) < p then (a : ℝ) - q / 2 + ((p : ℝ) - 1) / 2 - (i : ℕ)
      else (b : ℝ) + p / 2 + ((q : ℝ) - 1) / 2 - (((i : ℕ) : ℝ) - p) := by sorry
