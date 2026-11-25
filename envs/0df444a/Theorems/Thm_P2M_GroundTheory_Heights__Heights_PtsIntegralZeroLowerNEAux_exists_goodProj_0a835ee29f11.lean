-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PtsIntegralZeroLowerNEAux_exists_goodProj_0a835ee29f11
-- name    : P2M_GroundTheory_Heights__Heights_PtsIntegralZeroLowerNEAux_exists_goodProj_0a835ee29f11
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:15:34.924805+00:00
-- url     : https://prove2.me/theorems/a05a8888-fcd4-490d-b6ea-e0a4db0101c4
-- title:
--   P2 M Ground Theory Heights  Heights Pts Integral Zero Lower NEAux exists good Proj 0a835ee29f11: P2 M Ground Theory Heights  Heights Pts Integral Zero Lower NEAux exists good Proj 0a835ee29f11
-- statement:
--   The P2 M Ground Theory Heights  Heights Pts Integral Zero Lower NEAux exists good Proj 0a835ee29f11 construction uses the P2 M Ground Theory Heights  Heights Pts Integral Zero Lower NEAux exists good Proj 0a835ee29f11 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PPtsIntegralZeroLowerNE.lean#L56-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PPtsIntegralZeroLowerNE.lean#L56-L66

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeightNE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeB
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PPtsIntegralZeroLowerNE
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial MeasureTheory
noncomputable section
open GroundTheory.Heights₂.Heights.PtsIntegralZeroLowerNEAux
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_PtsIntegralZeroLowerNEAux_exists_goodProj_0a835ee29f11 {W : Ideal (MRing ι)} (hfin : Finite (McClasses W)) :
    ∃ Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (0 + 1) → ℂ), IsGoodProj W Ψ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PtsIntegralZeroLowerNEAux».«exists_goodProj» := P2M_GroundTheory_Heights__Heights_PtsIntegralZeroLowerNEAux_exists_goodProj_0a835ee29f11
