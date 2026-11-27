-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_LatticesAgree_hyps_48b85d0be2ae
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_LatticesAgree_hyps_48b85d0be2ae
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T13:24:51.676086+00:00
-- url     : https://prove2.me/theorems/39d478cd-4223-43a4-8094-18c32a68aa41
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model Lattices Agree hyps 48b85d0be2ae: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model Lattices Agree hyps
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model Lattices Agree hyps 48b85d0be2ae construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model Lattices Agree hyps 48b85d0be2ae property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/IsIsoPullbackObjUnitToUnit.lean#L462-L474
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/IsIsoPullbackObjUnitToUnit.lean#L462-L474

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_InvertibleSheaf
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_WeilDivisor
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_IsIsoPullbackObjUnitToUnit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
open CategoryTheory Opposite AlgebraicGeometry Limits TopologicalSpace MonoidalCategory
open GroundTheory.Arith.SchemeCoh
noncomputable section
universe u

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_LatticesAgree_hyps_48b85d0be2ae :
    IsIntegrallyClosed ℤ ∧ FiniteDimensional ℚ ℚ ∧ IsScalarTower ℤ ℚ ℚ ∧
    Module.Finite ℤ intLattice ∧ Module.Projective ℤ intLattice ∧
    Submodule.span ℚ (intLattice : Set ℚ) = ⊤ ∧
    (∀ p : Ideal ℤ, p.IsPrime → p.height = 1 → locSub intLattice p = locSub intLattice p) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Model».«LatticesAgree».«hyps» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_LatticesAgree_hyps_48b85d0be2ae
