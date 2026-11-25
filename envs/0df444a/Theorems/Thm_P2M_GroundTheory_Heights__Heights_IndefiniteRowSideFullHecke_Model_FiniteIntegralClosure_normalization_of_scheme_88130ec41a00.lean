-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_FiniteIntegralClosure_normalization_of_scheme_88130ec41a00
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_FiniteIntegralClosure_normalization_of_scheme_88130ec41a00
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:38:22.558736+00:00
-- url     : https://prove2.me/theorems/f8fbba3e-48d4-4ec7-a6dd-94453d2d7fb2
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model Finite Integral Closure normalization of scheme 88130ec41a00: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Heck
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model Finite Integral Closure normalization of scheme 88130ec41a00 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model Finite Integral Closure normalization of scheme 88130ec41a00 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/FiniteTypeSectionsOfIsFiniteTypeOverZ.lean#L77-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/FiniteTypeSectionsOfIsFiniteTypeOverZ.lean#L77-L116

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_FiniteIntegralClosure_normalization_of_scheme_88130ec41a00
    (h : ∀ (X : Scheme.{0}) [IsIntegral X], IsFiniteTypeOverZ X →
      ∀ (L : Type) [Field L] [Algebra X.functionField L] [FiniteDimensional X.functionField L]
        (U : X.Opens), IsAffineOpen U → ∀ hU : Nonempty U,
        let : Algebra Γ(X, U) L :=
          ((algebraMap X.functionField L).comp (@algebraMap Γ(X, U) X.functionField _ _ (by
            haveI := hU; infer_instance))).toAlgebra
        Module.Finite Γ(X, U) (integralClosure Γ(X, U) L)) :
    _root_.GroundTheory.Heights₂.Heights.Model.FiniteNormalization.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Model».«FiniteIntegralClosure».«normalization_of_scheme» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_FiniteIntegralClosure_normalization_of_scheme_88130ec41a00
