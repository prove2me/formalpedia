-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SegreCoordGoodProj_exists_monic_coeff_zero_ne_c6819acb24cb
-- name    : P2M_GroundTheory_Heights__Heights_SegreCoordGoodProj_exists_monic_coeff_zero_ne_c6819acb24cb
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:45:08.098647+00:00
-- url     : https://prove2.me/theorems/5e19ebc8-de63-486c-86e8-1e995f086c67
-- title:
--   P2 M Ground Theory Heights  Heights Segre Coord Good Proj exists monic coeff zero ne c6819acb24cb: P2 M Ground Theory Heights  Heights Segre Coord Good Proj exists monic coeff zero ne c6819acb24cb
-- statement:
--   The P2 M Ground Theory Heights  Heights Segre Coord Good Proj exists monic coeff zero ne c6819acb24cb construction uses the P2 M Ground Theory Heights  Heights Segre Coord Good Proj exists monic coeff zero ne c6819acb24cb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PSegreCoordGoodProj.lean#L17-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PSegreCoordGoodProj.lean#L17-L32

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

theorem P2M_GroundTheory_Heights__Heights_SegreCoordGoodProj_exists_monic_coeff_zero_ne_c6819acb24cb {A R : Type*} [CommRing A] [Nontrivial A] [CommRing R] [IsDomain R]
    (f : A →+* R) {x : R} (hx : x ≠ 0) (h : f.IsIntegralElem x) :
    ∃ p : Polynomial A, p.Monic ∧ p.eval₂ f x = 0 ∧ p.coeff 0 ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SegreCoordGoodProj».«exists_monic_coeff_zero_ne» := P2M_GroundTheory_Heights__Heights_SegreCoordGoodProj_exists_monic_coeff_zero_ne_c6819acb24cb
