-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_AnalyticLimit_levi_abs_le_local_acdff8994b08
-- name    : P2M_GroundTheory_Heights__Heights_AnalyticLimit_levi_abs_le_local_acdff8994b08
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T13:36:51.811181+00:00
-- url     : https://prove2.me/theorems/63b43e10-06d2-4e2f-8e8d-0a240bb04045
-- title:
--   P2 M Ground Theory Heights  Heights Analytic Limit levi abs le local acdff8994b08: P2 M Ground Theory Heights  Heights Analytic Limit levi abs le local acdff8994b08
-- statement:
--   The P2 M Ground Theory Heights  Heights Analytic Limit levi abs le local acdff8994b08 construction uses the P2 M Ground Theory Heights  Heights Analytic Limit levi abs le local acdff8994b08 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/AnalyticLimit/PKaehlerBound.lean#L34-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/AnalyticLimit/PKaehlerBound.lean#L34-L85

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_AnalyticLimit_KaehlerBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_AnalyticLimit_PKaehlerBound
import Theorems.Thm_ReciprocityTheory_AnForm_continuousOn_levi
import Theorems.Thm_ReciprocityTheory_AnForm_levi_add_smul
import Theorems.Thm_ReciprocityTheory_AnForm_levi_comp
import Theorems.Thm_ReciprocityTheory_AnForm_levi_congr
import Theorems.Thm_ReciprocityTheory_AnForm_levi_re_analytic
import Theorems.Thm_ReciprocityTheory_AnForm_levi_smul_dir
import Theorems.Thm_ReciprocityTheory_AnForm_levi_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.AnalyticLimit
open Filter Topology
open scoped ContDiff
open ReciprocityTheory.AnForm (levi levi_congr levi_comp levi_zero levi_smul_dir levi_add_smul
  levi_re_analytic continuousOn_levi)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsPosPot chartIdx)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (RegChartData)
noncomputable section
variable {D : ℕ} {X : Type} [TopologicalSpace X]

theorem P2M_GroundTheory_Heights__Heights_AnalyticLimit_levi_abs_le_local_acdff8994b08 (A : FinHolAtlas D X) (θ om : LocPot X) (hθ : IsPotential A θ)
    (hom : IsPotential A om) (hpos : IsPosPot A om) (p : X) (j : Fin A.n)
    (hp : p ∈ (A.chart j).source) :
    ∃ r > 0, ∃ M : ℝ, Metric.closedBall (A.chart j p) r ⊆
        (A.chart j).target ∩ (A.chart j).symm ⁻¹' (θ.U p ∩ om.U p) ∧
      ∀ y ∈ Metric.closedBall (A.chart j p) r, ∀ u : Fin D → ℂ,
        |levi (θ.φ p ∘ (A.chart j).symm) y u| ≤ M * levi (om.φ p ∘ (A.chart j).symm) y u := by sorry

alias «GroundTheory».«Heights₂».«Heights».«AnalyticLimit».«levi_abs_le_local» := P2M_GroundTheory_Heights__Heights_AnalyticLimit_levi_abs_le_local_acdff8994b08
