-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_FiniteIntegralClosure_scheme_of_alg_f4618e49e8db
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_FiniteIntegralClosure_scheme_of_alg_f4618e49e8db
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:23:00.170147+00:00
-- url     : https://prove2.me/theorems/26dfd776-487e-4f87-add9-2f8513fc1714
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model Finite Integral Closure scheme of alg f4618e49e8db: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model Fi
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model Finite Integral Closure scheme of alg f4618e49e8db construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model Finite Integral Closure scheme of alg f4618e49e8db property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/FiniteTypeSectionsOfIsFiniteTypeOverZ.lean#L34-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/FiniteTypeSectionsOfIsFiniteTypeOverZ.lean#L34-L52

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_FiniteIntegralClosure_scheme_of_alg_f4618e49e8db
    (h : ∀ (A K L : Type) [CommRing A] [IsDomain A] [Algebra.FiniteType ℤ A] [Field K]
      [Algebra A K] [IsFractionRing A K] [Field L] [Algebra K L] [FiniteDimensional K L]
      [Algebra A L] [IsScalarTower A K L], Module.Finite A (integralClosure A L)) :
    ∀ (X : Scheme.{0}) [IsIntegral X], IsFiniteTypeOverZ X →
      ∀ (L : Type) [Field L] [Algebra X.functionField L] [FiniteDimensional X.functionField L]
        (U : X.Opens), IsAffineOpen U → ∀ hU : Nonempty U,
        let : Algebra Γ(X, U) L :=
          ((algebraMap X.functionField L).comp (@algebraMap Γ(X, U) X.functionField _ _ (by
            haveI := hU; infer_instance))).toAlgebra
        Module.Finite Γ(X, U) (integralClosure Γ(X, U) L) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Model».«FiniteIntegralClosure».«scheme_of_alg» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_FiniteIntegralClosure_scheme_of_alg_f4618e49e8db
