-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_AnalyticLimit_hessC_finset_sum_8ccaf9ba300e
-- name    : P2M_GroundTheory_Heights__Heights_AnalyticLimit_hessC_finset_sum_8ccaf9ba300e
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T13:33:19.496283+00:00
-- url     : https://prove2.me/theorems/9a316c74-3585-56d1-8e46-78677882576f
-- title:
--   P2 M Ground Theory Heights  Heights Analytic Limit hess C finset sum 8ccaf9ba300e: P2 M Ground Theory Heights  Heights Analytic Limit hess C finset sum 8ccaf9ba300e
-- statement:
--   The P2 M Ground Theory Heights  Heights Analytic Limit hess C finset sum 8ccaf9ba300e construction uses the P2 M Ground Theory Heights  Heights Analytic Limit hess C finset sum 8ccaf9ba300e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/AnalyticLimit/EnergySum.lean#L54-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/AnalyticLimit/EnergySum.lean#L54-L66

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

theorem P2M_GroundTheory_Heights__Heights_AnalyticLimit_hessC_finset_sum_8ccaf9ba300e {ι : Type*} (s : Finset ι) (c : ι → ℝ) (f : ι → (Fin D → ℂ) → ℝ)
    (z : Fin D → ℂ) (hf : ∀ i ∈ s, ContDiffAt ℝ 2 (f i) z) :
    hessC (fun w => ∑ i ∈ s, c i * f i w) z = ∑ i ∈ s, (c i : ℂ) • hessC (f i) z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«AnalyticLimit».«hessC_finset_sum» := P2M_GroundTheory_Heights__Heights_AnalyticLimit_hessC_finset_sum_8ccaf9ba300e
