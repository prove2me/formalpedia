-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PointsBilinear_integrable_fibreSum_ca6e862a0c18
-- name    : P2M_GroundTheory_Heights__Heights_PointsBilinear_integrable_fibreSum_ca6e862a0c18
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:15:16.934623+00:00
-- url     : https://prove2.me/theorems/6c0661b7-2ef9-4171-99d2-0e7a4a7fb91d
-- title:
--   P2 M Ground Theory Heights  Heights Points Bilinear integrable fibre Sum ca6e862a0c18: P2 M Ground Theory Heights  Heights Points Bilinear integrable fibre Sum ca6e862a0c18
-- statement:
--   The P2 M Ground Theory Heights  Heights Points Bilinear integrable fibre Sum ca6e862a0c18 construction uses the P2 M Ground Theory Heights  Heights Points Bilinear integrable fibre Sum ca6e862a0c18 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PPtsBilinear.lean#L132-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PPtsBilinear.lean#L132-L164

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_CasChainA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSheet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StPtsBilinear
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PtsIntegrable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PPtsBilinear
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
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo
open scoped ContDiff
open GroundTheory.Heights₂.Heights.PointsBilinear
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_PointsBilinear_integrable_fibreSum_ca6e862a0c18 (hInt : PtsIntegrableStatement) {P : Ideal (MRing ι)} {n : ℕ}
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1 + 1) → ℂ)) (L : Fin n → HermLine ι)
    {f g : ((Σ k, ι k) → ℂ) → ℝ} (hP : IsArithVar P (n + 2)) (hΨ : IsGoodProj P Ψ)
    (hL : ∀ j, IsSmoothHerm (L j)) (hf : IsDegZeroSmooth f) (hg : IsDegZeroSmooth g) :
    Integrable (fun y => ∑ᶠ w ∈ fibre P Ψ y, sheetDensity P Ψ (Fin.cons f (pot L)) g y w) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PointsBilinear».«integrable_fibreSum» := P2M_GroundTheory_Heights__Heights_PointsBilinear_integrable_fibreSum_ca6e862a0c18
