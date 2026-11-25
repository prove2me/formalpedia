-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_AnalyticLimit_tvInt_lincomb_le_5b348dfe4313
-- name    : P2M_GroundTheory_Heights__Heights_AnalyticLimit_tvInt_lincomb_le_5b348dfe4313
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T13:33:25.523571+00:00
-- url     : https://prove2.me/theorems/1c108ee3-16bc-51f0-95c9-931b62eeb8d3
-- title:
--   P2 M Ground Theory Heights  Heights Analytic Limit tv Int lincomb le 5b348dfe4313: P2 M Ground Theory Heights  Heights Analytic Limit tv Int lincomb le 5b348dfe4313
-- statement:
--   The P2 M Ground Theory Heights  Heights Analytic Limit tv Int lincomb le 5b348dfe4313 construction uses the P2 M Ground Theory Heights  Heights Analytic Limit tv Int lincomb le 5b348dfe4313 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/AnalyticLimit/EnergySum.lean#L106-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/AnalyticLimit/EnergySum.lean#L106-L147

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
variable {X : Type*} [TopologicalSpace X]

theorem P2M_GroundTheory_Heights__Heights_AnalyticLimit_tvInt_lincomb_le_5b348dfe4313 (A : FinHolAtlas D X) (Yo : Set X) {m : ℕ} (P : Fin m → LocPot X)
    (a : Fin D → Fin m → ℝ) (hpot : ∀ i, IsPotential A (P i)) (hnn : ∀ i, FormNonneg A Yo (P i))
    (hint : ∀ (σ : Fin D → Fin m) (Q : ChartPartition A) (j : Fin A.n), IntegrableOn (fun y =>
      Q.χ j ((A.chart j).symm y) * Yo.indicator 1 ((A.chart j).symm y) *
        locDens A (fun k => P (σ k)) j y) (A.chart j).target) :
    tvInt A (fun k => lincomb m (a k) P) (Yo.indicator 1) ≤
      ∑ σ : Fin D → Fin m, (∏ k, |a k (σ k)|) * mInt A (fun k => P (σ k)) (Yo.indicator 1) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«AnalyticLimit».«tvInt_lincomb_le» := P2M_GroundTheory_Heights__Heights_AnalyticLimit_tvInt_lincomb_le_5b348dfe4313
