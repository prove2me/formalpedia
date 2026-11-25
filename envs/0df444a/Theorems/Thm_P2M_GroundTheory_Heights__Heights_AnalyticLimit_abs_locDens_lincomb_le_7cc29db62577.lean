-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_AnalyticLimit_abs_locDens_lincomb_le_7cc29db62577
-- name    : P2M_GroundTheory_Heights__Heights_AnalyticLimit_abs_locDens_lincomb_le_7cc29db62577
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T13:33:30.429473+00:00
-- url     : https://prove2.me/theorems/e4ef676b-2307-50fc-a666-4404308b36e4
-- title:
--   P2 M Ground Theory Heights  Heights Analytic Limit abs loc Dens lincomb le 7cc29db62577: P2 M Ground Theory Heights  Heights Analytic Limit abs loc Dens lincomb le 7cc29db62577
-- statement:
--   The P2 M Ground Theory Heights  Heights Analytic Limit abs loc Dens lincomb le 7cc29db62577 construction uses the P2 M Ground Theory Heights  Heights Analytic Limit abs loc Dens lincomb le 7cc29db62577 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/AnalyticLimit/EnergySum.lean#L70-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/AnalyticLimit/EnergySum.lean#L70-L104

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

theorem P2M_GroundTheory_Heights__Heights_AnalyticLimit_abs_locDens_lincomb_le_7cc29db62577 (A : FinHolAtlas D X) (Yo : Set X) {m : ℕ} (P : Fin m → LocPot X)
    (a : Fin D → Fin m → ℝ) (hpot : ∀ i, IsPotential A (P i)) (hnn : ∀ i, FormNonneg A Yo (P i))
    (j : Fin A.n) (y : Fin D → ℂ) (hy : y ∈ (A.chart j).target) (hY : (A.chart j).symm y ∈ Yo) :
    |locDens A (fun k => lincomb m (a k) P) j y| ≤
      ∑ σ : Fin D → Fin m, (∏ k, |a k (σ k)|) * locDens A (fun k => P (σ k)) j y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«AnalyticLimit».«abs_locDens_lincomb_le» := P2M_GroundTheory_Heights__Heights_AnalyticLimit_abs_locDens_lincomb_le_7cc29db62577
