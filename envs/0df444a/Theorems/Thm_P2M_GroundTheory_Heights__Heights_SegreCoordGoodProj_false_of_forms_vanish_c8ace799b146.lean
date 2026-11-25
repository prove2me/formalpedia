-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SegreCoordGoodProj_false_of_forms_vanish_c8ace799b146
-- name    : P2M_GroundTheory_Heights__Heights_SegreCoordGoodProj_false_of_forms_vanish_c8ace799b146
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:37:40.318274+00:00
-- url     : https://prove2.me/theorems/3889431a-9aa7-4962-8725-edd3407f3116
-- title:
--   P2 M Ground Theory Heights  Heights Segre Coord Good Proj false of forms vanish c8ace799b146: P2 M Ground Theory Heights  Heights Segre Coord Good Proj false of forms vanish c8ace799b146
-- statement:
--   The P2 M Ground Theory Heights  Heights Segre Coord Good Proj false of forms vanish c8ace799b146 construction uses the P2 M Ground Theory Heights  Heights Segre Coord Good Proj false of forms vanish c8ace799b146 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PSegreCoordGoodProj.lean#L60-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PSegreCoordGoodProj.lean#L60-L92

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

theorem P2M_GroundTheory_Heights__Heights_SegreCoordGoodProj_false_of_forms_vanish_c8ace799b146 (P : Ideal (MRing ι)) (hhom : IsMultiHomogIdeal P) (k0 : K) {r : ℕ}
    (L : Fin r → ((k : K) → ι k) → ℚ) (hL : ∀ t, IntOver ℚ (forms (segQ P) L) (segQ P t))
    {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts P) (hV : ∀ j, ∑ t, (L j t : ℂ) * segre z t = 0) : False := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SegreCoordGoodProj».«false_of_forms_vanish» := P2M_GroundTheory_Heights__Heights_SegreCoordGoodProj_false_of_forms_vanish_c8ace799b146
