-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_isMultiProjPrime_primeOfOne_739683a29f58
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_isMultiProjPrime_primeOfOne_739683a29f58
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:09:50.213451+00:00
-- url     : https://prove2.me/theorems/0002be83-0ccc-49b7-a415-eda61c31b12f
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman is Multi Proj Prime prime Of One 739683a29f58: P2 M Ground Theory Heights  Heights Kleiman is Multi Proj Prime prime Of One 739683a29f58
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman is Multi Proj Prime prime Of One 739683a29f58 construction uses the P2 M Ground Theory Heights  Heights Kleiman is Multi Proj Prime prime Of One 739683a29f58 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/Objects.lean#L427-L460
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/Objects.lean#L427-L460

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsSemipositiveOn
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Objects
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u v w
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω]
variable {N : ℕ} (x : Fin (N + 1) → Ω)
open NumbersDVR

theorem P2M_GroundTheory_Heights__Heights_Kleiman_isMultiProjPrime_primeOfOne_739683a29f58 (hx : x ≠ 0) : IsMultiProjPrime (primeOfOne (S := S) x) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«isMultiProjPrime_primeOfOne» := P2M_GroundTheory_Heights__Heights_Kleiman_isMultiProjPrime_primeOfOne_739683a29f58
