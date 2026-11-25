-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_PotentialCharts_glue_eq_pad_7acbd7ed4c16
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_PotentialCharts_glue_eq_pad_7acbd7ed4c16
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T13:16:14.024627+00:00
-- url     : https://prove2.me/theorems/6ea08f5e-83ea-5103-b23e-3c6901750bd7
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Regular Potential Charts glue eq pad 7acbd7ed4c16: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Regular Potenti
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Regular Potential Charts glue eq pad 7acbd7ed4c16 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Regular Potential Charts glue eq pad 7acbd7ed4c16 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/ToPotentialChartsChartFun.lean#L294-L299
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/ToPotentialChartsChartFun.lean#L294-L299

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ContinuousTmaxShift
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_IsOpenKappaOpenNeighbourhood
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_ToPotentialChartsChartFun
import Theorems.Thm_P2M_ReciprocityTheory_AnForm_A_abs_le_of_k__ne_3ed6a6aa9d98
import Theorems.Thm_P2M_ReciprocityTheory_AnForm_A_k__integral_37214bfa7034
import Theorems.Thm_ReciprocityTheory_AnForm_A_le_tmax
import Theorems.Thm_ReciprocityTheory_AnForm_A_tmax_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular
open MeasureTheory Metric Set
open scoped ContDiff
open ReciprocityTheory.AnForm (levi)
open ReciprocityTheory.AnForm.A (Mollifier molli regMax tmax kθ le_tmax tmax_le kθ_integral abs_le_of_kθ_ne)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsPosPot IsCompatChart)
open GroundTheory.Heights₂.Heights.Regular (PotentialCharts)
noncomputable section
variable {D : ℕ} {X : Type*} [TopologicalSpace X] {A : FinHolAtlas D X}
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular.PotentialCharts
variable (P : PotentialCharts A)
open Classical

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_PotentialCharts_glue_eq_pad_7acbd7ed4c16 (a : Fin P.N → X → ℝ) {ε : ℝ} (hε : 0 ≤ ε) (x : X) {c : Fin P.N}
    (hc : x ∈ P.mid c) :
    P.glue a ε x = (haveI : Nonempty (Fin P.N) := ⟨c⟩
      regMax ε (fun j => if x ∈ P.mid j then a j x else a c x - ε)) + ε / 2 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Regular».«PotentialCharts».«glue_eq_pad» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_PotentialCharts_glue_eq_pad_7acbd7ed4c16
