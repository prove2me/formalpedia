-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_finiteType_sections_of_isFiniteTypeOverZ_dd9622bb96c7
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_finiteType_sections_of_isFiniteTypeOverZ_dd9622bb96c7
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:38:36.594418+00:00
-- url     : https://prove2.me/theorems/527508fa-1144-4656-ad72-931878e10892
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model finite Type sections of is Finite Type Over Z dd9622bb96c7: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model finite Type sections of is Finite Type Over Z dd9622bb96c7 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model finite Type sections of is Finite Type Over Z dd9622bb96c7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/FiniteTypeSectionsOfIsFiniteTypeOverZ.lean#L22-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/FiniteTypeSectionsOfIsFiniteTypeOverZ.lean#L22-L32

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_finiteType_sections_of_isFiniteTypeOverZ_dd9622bb96c7 {X : Scheme.{0}} (hX : IsFiniteTypeOverZ X)
    {U : X.Opens} (hU : IsAffineOpen U) : Algebra.FiniteType ℤ Γ(X, U) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Model».«finiteType_sections_of_isFiniteTypeOverZ» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_finiteType_sections_of_isFiniteTypeOverZ_dd9622bb96c7
