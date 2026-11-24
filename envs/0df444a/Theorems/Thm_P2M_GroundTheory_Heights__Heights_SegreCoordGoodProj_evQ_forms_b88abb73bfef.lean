-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SegreCoordGoodProj_evQ_forms_b88abb73bfef
-- name    : P2M_GroundTheory_Heights__Heights_SegreCoordGoodProj_evQ_forms_b88abb73bfef
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:33:07.208728+00:00
-- url     : https://prove2.me/theorems/7a3a9ce7-8e8d-4695-b2dc-1b8564fd6f9e
-- title:
--   P2 M Ground Theory Heights  Heights Segre Coord Good Proj ev Q forms b88abb73bfef: P2 M Ground Theory Heights  Heights Segre Coord Good Proj ev Q forms b88abb73bfef
-- statement:
--   The P2 M Ground Theory Heights  Heights Segre Coord Good Proj ev Q forms b88abb73bfef construction uses the P2 M Ground Theory Heights  Heights Segre Coord Good Proj ev Q forms b88abb73bfef property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PSegreCoordGoodProj.lean#L46-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PSegreCoordGoodProj.lean#L46-L49

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGood
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StSegreCoordGoodProj
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PSegreCoordGoodProj
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
open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo
open GroundTheory.Heights₂.Heights.SegreCoordGoodProj
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_SegreCoordGoodProj_evQ_forms_b88abb73bfef (P : Ideal (MRing ι)) (z : (Σ k, ι k) → ℂ) (hz : z ∈ mcPts P) {r : ℕ}
    (L : Fin r → ((k : K) → ι k) → ℚ) (j : Fin r) :
    evQ P z hz (forms (segQ P) L j) = ∑ t, (L j t : ℂ) * segre z t := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SegreCoordGoodProj».«evQ_forms» := P2M_GroundTheory_Heights__Heights_SegreCoordGoodProj_evQ_forms_b88abb73bfef
