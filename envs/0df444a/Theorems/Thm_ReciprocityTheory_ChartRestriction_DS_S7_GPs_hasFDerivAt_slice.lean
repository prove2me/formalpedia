-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_GPs_hasFDerivAt_slice
-- name    : ReciprocityTheory.ChartRestriction.DS.S7.GPs.hasFDerivAt_slice
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T13:04:32.554536+00:00
-- url     : https://prove2.me/theorems/9873e454-a751-40bc-a7c4-6a01c3bcd943
-- title:
--   GPs: has FDeriv At slice
-- statement:
--   The GPs construction uses the has FDeriv At slice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/GelfandPsB.lean#L117-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/GelfandPsB.lean#L117-L123

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_GelfandPsA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ContinuousOnFderivPhiP
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_GelfandPsB
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
open scoped ContDiff
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
open ReciprocityTheory.ChartRestriction.DS.S7.GPs

theorem ReciprocityTheory.ChartRestriction.DS.S7.GPs.hasFDerivAt_slice (q : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ)
    (x : Matrix (Fin n) (Fin n) ℂ) :
    HasFDerivAt (fun y : Matrix (Fin n) (Fin n) ℂ => ((y, q) : Matrix (Fin n) (Fin n) ℂ ×
      Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ)) (I0 n) x := by sorry
