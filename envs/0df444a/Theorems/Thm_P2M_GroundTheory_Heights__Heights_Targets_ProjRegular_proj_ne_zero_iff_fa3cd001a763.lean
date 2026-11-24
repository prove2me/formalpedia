-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ProjRegular_proj_ne_zero_iff_fa3cd001a763
-- name    : P2M_GroundTheory_Heights__Heights_Targets_ProjRegular_proj_ne_zero_iff_fa3cd001a763
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T03:55:44.258674+00:00
-- url     : https://prove2.me/theorems/aead0e62-072d-4b52-9cf1-db31691236e2
-- title:
--   P2 M Ground Theory Heights  Heights Targets Proj Regular proj ne zero iff fa3cd001a763: P2 M Ground Theory Heights  Heights Targets Proj Regular proj ne zero iff fa3cd001a763
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Proj Regular proj ne zero iff fa3cd001a763 construction uses the P2 M Ground Theory Heights  Heights Targets Proj Regular proj ne zero iff fa3cd001a763 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PProjRegular.lean#L33-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PProjRegular.lean#L33-L36

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

theorem P2M_GroundTheory_Heights__Heights_Targets_ProjRegular_proj_ne_zero_iff_fa3cd001a763 {x y : R.X} (hy : y ∈ R.U x) :
    Ψ (segre (R.lift y y)) 0 ≠ 0 ↔ Ψ (segre (R.lift x y)) 0 ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«ProjRegular».«proj_ne_zero_iff» := P2M_GroundTheory_Heights__Heights_Targets_ProjRegular_proj_ne_zero_iff_fa3cd001a763
