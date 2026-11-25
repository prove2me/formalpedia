-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_GoodChartModel_pow_mem_888f6687f3f9
-- name    : P2M_GroundTheory_Heights__Heights_GoodChartModel_pow_mem_888f6687f3f9
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T14:21:10.327226+00:00
-- url     : https://prove2.me/theorems/5ec47789-3f6b-49d5-94e2-628e94399684
-- title:
--   P2 M Ground Theory Heights  Heights Good Chart Model pow mem 888f6687f3f9: P2 M Ground Theory Heights  Heights Good Chart Model pow mem 888f6687f3f9
-- statement:
--   The P2 M Ground Theory Heights  Heights Good Chart Model pow mem 888f6687f3f9 construction uses the P2 M Ground Theory Heights  Heights Good Chart Model pow mem 888f6687f3f9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PGoodChartModel.lean#L32-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PGoodChartModel.lean#L32-L81

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StGoodChartModel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StGoodChartZeroSet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StGoodChartDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteProjHomInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PConeAvoidsFinite
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PGoodChartModel
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
open GroundTheory.Heights₂.Heights.GoodChartModel

theorem P2M_GroundTheory_Heights__Heights_GoodChartModel_pow_mem_888f6687f3f9 {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {P : Ideal (MRing ι)} {e m : ℕ} {σ : Fin m ≃ ((k : K) → ι k)}
    {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)}
    (hP : IsArithVar P (e + 1)) (hΨ : IsGoodProj P Ψ)
    {J : Ideal (MvPolynomial (Fin m) ℂ)} (hJ : projChartIdeal P σ Ψ ≤ J) (a : Fin m) :
    ∃ r : ℕ, (X a ^ r : MvPolynomial (Fin m) ℂ) ∈ leadIdeal J ⊔ linIdeal (chartProjMatrix σ Ψ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«GoodChartModel».«pow_mem» := P2M_GroundTheory_Heights__Heights_GoodChartModel_pow_mem_888f6687f3f9
