-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_hasDerivAt_line
-- name    : ReciprocityTheory.ChartRestriction.DS.S7.hasDerivAt_line
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:06:58.174644+00:00
-- url     : https://prove2.me/theorems/80c9d2ff-eafd-40c7-8a60-87bd28ab8223
-- title:
--   S7: has Deriv At line
-- statement:
--   The S7 construction uses the has Deriv At line property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/PhiCasA.lean#L51-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/PhiCasA.lean#L51-L60

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiCasA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix
open scoped ContDiff
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}

theorem ReciprocityTheory.ChartRestriction.DS.S7.hasDerivAt_line {F : Matrix (Fin n) (Fin n) ℂ → ℂ} {z : Matrix (Fin n) (Fin n) ℂ}
    (hF : DifferentiableAt ℂ F z) (v : Matrix (Fin n) (Fin n) ℂ) :
    HasDerivAt (fun t : ℂ => F (z + t • v)) (fderiv ℂ F z v) 0 := by sorry
