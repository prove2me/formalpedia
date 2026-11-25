-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SegreCoordGoodProj_evQ_aeval_18cf22fe483c
-- name    : P2M_GroundTheory_Heights__Heights_SegreCoordGoodProj_evQ_aeval_18cf22fe483c
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:39:05.479342+00:00
-- url     : https://prove2.me/theorems/0ba8af0b-4a2b-5ed8-a93d-12122203ce93
-- title:
--   P2 M Ground Theory Heights  Heights Segre Coord Good Proj ev Q aeval 18cf22fe483c: P2 M Ground Theory Heights  Heights Segre Coord Good Proj ev Q aeval 18cf22fe483c
-- statement:
--   The P2 M Ground Theory Heights  Heights Segre Coord Good Proj ev Q aeval 18cf22fe483c construction uses the P2 M Ground Theory Heights  Heights Segre Coord Good Proj ev Q aeval 18cf22fe483c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PSegreCoordGoodProj.lean#L52-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PSegreCoordGoodProj.lean#L52-L58

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
omit [Fintype K] [DecidableEq K] [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_SegreCoordGoodProj_evQ_aeval_18cf22fe483c (P : Ideal (MRing ι)) (z : (Σ k, ι k) → ℂ) (hz : z ∈ mcPts P) {r : ℕ}
    (ℓ : Fin r → MvPolynomial (Σ k, ι k) ℚ ⧸ qIdeal P) (F : MvPolynomial (Fin r) ℚ) :
    evQ P z hz (aeval ℓ F) = aeval (fun j => evQ P z hz (ℓ j)) F := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SegreCoordGoodProj».«evQ_aeval» := P2M_GroundTheory_Heights__Heights_SegreCoordGoodProj_evQ_aeval_18cf22fe483c
