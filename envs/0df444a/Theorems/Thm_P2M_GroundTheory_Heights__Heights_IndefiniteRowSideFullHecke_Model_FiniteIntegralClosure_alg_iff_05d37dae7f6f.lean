-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_FiniteIntegralClosure_alg_iff_05d37dae7f6f
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_FiniteIntegralClosure_alg_iff_05d37dae7f6f
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:22:48.354023+00:00
-- url     : https://prove2.me/theorems/b4169c1e-ae0c-4194-89c2-b0aebb0fa76c
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model Finite Integral Closure alg iff 05d37dae7f6f: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model Finite I
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model Finite Integral Closure alg iff 05d37dae7f6f construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model Finite Integral Closure alg iff 05d37dae7f6f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/FiniteTypeSectionsOfIsFiniteTypeOverZ.lean#L12-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/FiniteTypeSectionsOfIsFiniteTypeOverZ.lean#L12-L20

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_IsIsoPullbackObjUnitToUnit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_FiniteTypeSectionsOfIsFiniteTypeOverZ
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
open CategoryTheory Opposite AlgebraicGeometry
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_FiniteIntegralClosure_alg_iff_05d37dae7f6f :
    (∀ (A : Type) [CommRing A] [IsDomain A] [Algebra.FiniteType ℤ A]
      (K : Type) [Field K] [Algebra A K] [IsFractionRing A K]
      (L : Type) [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra A L] [IsScalarTower A K L],
      Module.Finite A (integralClosure A L)) ↔
    (∀ (A K L : Type) [CommRing A] [IsDomain A] [Algebra.FiniteType ℤ A] [Field K] [Algebra A K]
      [IsFractionRing A K] [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra A L]
      [IsScalarTower A K L], Module.Finite A (integralClosure A L)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Model».«FiniteIntegralClosure».«alg_iff» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_FiniteIntegralClosure_alg_iff_05d37dae7f6f
