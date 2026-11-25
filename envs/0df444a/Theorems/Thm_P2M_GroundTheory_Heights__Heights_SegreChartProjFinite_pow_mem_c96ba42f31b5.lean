-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SegreChartProjFinite_pow_mem_c96ba42f31b5
-- name    : P2M_GroundTheory_Heights__Heights_SegreChartProjFinite_pow_mem_c96ba42f31b5
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T16:34:50.983193+00:00
-- url     : https://prove2.me/theorems/3e3bff44-f478-5635-a312-a5fb4bf66a6f
-- title:
--   P2 M Ground Theory Heights  Heights Segre Chart Proj Finite pow mem c96ba42f31b5: P2 M Ground Theory Heights  Heights Segre Chart Proj Finite pow mem c96ba42f31b5
-- statement:
--   The P2 M Ground Theory Heights  Heights Segre Chart Proj Finite pow mem c96ba42f31b5 construction uses the P2 M Ground Theory Heights  Heights Segre Chart Proj Finite pow mem c96ba42f31b5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PSegreChartProjFinite.lean#L29-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PSegreChartProjFinite.lean#L29-L78

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StSegreChartProjFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PSegreChartDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteProjHomInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PConeAvoidsFinite
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PSegreChartProjFinite
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_segre_rel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsArithVar IsGoodProj mcPts segre segre_rel)
open ComplexSets MvPolynomial Matrix

theorem P2M_GroundTheory_Heights__Heights_SegreChartProjFinite_pow_mem_c96ba42f31b5 {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {P : Ideal (MRing ι)} {e m : ℕ} {σ : Fin m ≃ ((k : K) → ι k)} {i : (k : K) → ι k}
    {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)}
    (hP : IsArithVar P (e + 1)) (hΨ : IsGoodProj P Ψ) (hΨ0 : ∀ w, Ψ w 0 = w i)
    {J : Ideal (MvPolynomial (Fin m) ℂ)} (hJ : J ∈ segreChartComponents P σ i) (a : Fin m) :
    ∃ r : ℕ, (X a ^ r : MvPolynomial (Fin m) ℂ) ∈ leadIdeal J ⊔ linIdeal (chartProjMatrix σ Ψ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SegreChartProjFinite».«pow_mem» := P2M_GroundTheory_Heights__Heights_SegreChartProjFinite_pow_mem_c96ba42f31b5
