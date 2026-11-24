-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ProjRegular_projCoord_eq_954a26e906c8
-- name    : P2M_GroundTheory_Heights__Heights_Targets_ProjRegular_projCoord_eq_954a26e906c8
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T03:58:17.625056+00:00
-- url     : https://prove2.me/theorems/f7a602b1-7ec0-4208-88b5-960f66da465e
-- title:
--   P2 M Ground Theory Heights  Heights Targets Proj Regular proj Coord eq 954a26e906c8: P2 M Ground Theory Heights  Heights Targets Proj Regular proj Coord eq 954a26e906c8
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Proj Regular proj Coord eq 954a26e906c8 construction uses the P2 M Ground Theory Heights  Heights Targets Proj Regular proj Coord eq 954a26e906c8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PProjRegular.lean#L26-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PProjRegular.lean#L26-L31

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeH
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsProjRegular
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PProjRegular
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M
open GroundTheory.Heights₂.Heights.Targets.ProjRegular
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P J : Ideal (MRing ι)}
  {n : ℕ} {R : AnLogRes P J (n + 1)} (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ))

theorem P2M_GroundTheory_Heights__Heights_Targets_ProjRegular_projCoord_eq_954a26e906c8 {x y : R.X} (hy : y ∈ R.U x) :
    projCoord R Ψ y = fun i => Ψ (segre (R.lift x y)) i.succ / Ψ (segre (R.lift x y)) 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«ProjRegular».«projCoord_eq» := P2M_GroundTheory_Heights__Heights_Targets_ProjRegular_projCoord_eq_954a26e906c8
