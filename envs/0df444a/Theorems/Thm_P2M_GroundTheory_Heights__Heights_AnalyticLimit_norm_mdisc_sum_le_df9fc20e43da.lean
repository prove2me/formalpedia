-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_AnalyticLimit_norm_mdisc_sum_le_df9fc20e43da
-- name    : P2M_GroundTheory_Heights__Heights_AnalyticLimit_norm_mdisc_sum_le_df9fc20e43da
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T13:41:08.178023+00:00
-- url     : https://prove2.me/theorems/e48273ac-8e8b-48d2-bd2d-7a709159ee8b
-- title:
--   P2 M Ground Theory Heights  Heights Analytic Limit norm mdisc sum le df9fc20e43da: P2 M Ground Theory Heights  Heights Analytic Limit norm mdisc sum le df9fc20e43da
-- statement:
--   The P2 M Ground Theory Heights  Heights Analytic Limit norm mdisc sum le df9fc20e43da construction uses the P2 M Ground Theory Heights  Heights Analytic Limit norm mdisc sum le df9fc20e43da property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/AnalyticLimit/EnergySum.lean#L40-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/AnalyticLimit/EnergySum.lean#L40-L52

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_HessCIsHermitian
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ProjectiveLinePartitionContinuousCoe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_AnalyticLimit_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_AnalyticLimit_EnergySum
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
open MeasureTheory
open scoped ContDiff ComplexOrder
open ReciprocityTheory.AnForm (hessC maDens mdisc levi)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential mInt ChartPartition locDens integralWith)
noncomputable section
variable {D : ℕ}

theorem P2M_GroundTheory_Heights__Heights_AnalyticLimit_norm_mdisc_sum_le_df9fc20e43da {m : ℕ} (a : Fin D → Fin m → ℝ)
    (B : Fin D → Fin m → Matrix (Fin D) (Fin D) ℂ) (hB : ∀ k i, (B k i).PosSemidef) :
    ‖mdisc (fun k => ∑ i, (a k i : ℂ) • B k i)‖ ≤
      ∑ σ : Fin D → Fin m, (∏ k, |a k (σ k)|) * (mdisc fun k => B k (σ k)).re := by sorry

alias «GroundTheory».«Heights₂».«Heights».«AnalyticLimit».«norm_mdisc_sum_le» := P2M_GroundTheory_Heights__Heights_AnalyticLimit_norm_mdisc_sum_le_df9fc20e43da
