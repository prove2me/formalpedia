-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_IdA_contDiffAt_dPhi2
-- name    : ReciprocityTheory.ChartRestriction.DS.S7.IdA.contDiffAt_dPhi2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:13:32.296274+00:00
-- url     : https://prove2.me/theorems/948a35b7-b985-4819-8514-6542a63b85bc
-- title:
--   Id A: cont Diff At d Phi2
-- statement:
--   The Id A construction uses the cont Diff At d Phi2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/IdThmA.lean#L98-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/IdThmA.lean#L98-L103

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiCasA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_KFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IdThmA
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
variable {n : ℕ} {ε : Fin n → Bool} {Λ : Fin n → ℝ}
open ReciprocityTheory.ChartRestriction.DS.S7.IdA

theorem ReciprocityTheory.ChartRestriction.DS.S7.IdA.contDiffAt_dPhi2 (μ : Fin n → ℤ) {p : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ}
    (hp : p.1 ∈ OmegaSet n) : ContDiffAt ℂ 1 (dPhi2 μ) p := by sorry
