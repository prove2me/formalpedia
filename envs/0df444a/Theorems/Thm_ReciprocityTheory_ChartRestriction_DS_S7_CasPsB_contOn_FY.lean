-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_CasPsB_contOn_FY
-- name    : ReciprocityTheory.ChartRestriction.DS.S7.CasPsB.contOn_FY
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:03:59.110143+00:00
-- url     : https://prove2.me/theorems/311387e5-81ce-4851-b66b-9b6d91d766ed
-- title:
--   Cas Ps B: cont On FY
-- statement:
--   The Cas Ps B construction uses the cont On FY property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/CasPsB.lean#L141-L174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/CasPsB.lean#L141-L174

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ContinuousOnFderivPhiP
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiCas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_CasPsA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_CasPsB
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
open ReciprocityTheory.ChartRestriction.DS.S7.CasPsB
local notation "𝕄" => Fin n → Fin n → ℂ
variable {ε : Fin n → Bool} {Λ : Fin n → ℝ}

theorem ReciprocityTheory.ChartRestriction.DS.S7.CasPsB.contOn_FY (T : KType ε Λ) (μ : Fin n → ℤ) (Y : Matrix (Fin n) (Fin n) ℂ)
    {U : Set (Matrix (Fin n) (Fin n) ℂ)}
    (hΩ : ∀ z ∈ U, ∀ k : KG ε, toMK k⁻¹ * z * toMK k ∈ OmegaSet n) :
    ContinuousOn (fun p : Matrix (Fin n) (Fin n) ℂ × KG ε => FY T μ Y p.1 p.2) (U ×ˢ Set.univ) ∧
      ContinuousOn (fun p : Matrix (Fin n) (Fin n) ℂ × KG ε => FY' T μ Y p.1 p.2) (U ×ˢ Set.univ) := by sorry
