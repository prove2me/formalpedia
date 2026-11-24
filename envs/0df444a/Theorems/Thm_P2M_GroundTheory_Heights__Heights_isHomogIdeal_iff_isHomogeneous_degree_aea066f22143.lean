-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_isHomogIdeal_iff_isHomogeneous_degree_aea066f22143
-- name    : P2M_GroundTheory_Heights__Heights_isHomogIdeal_iff_isHomogeneous_degree_aea066f22143
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:46:58.1448+00:00
-- url     : https://prove2.me/theorems/b2e0d51d-6616-49cc-b9ee-8015aa734da7
-- title:
--   P2 M Ground Theory Heights  Heights is Homog Ideal iff is Homogeneous degree aea066f22143: P2 M Ground Theory Heights  Heights is Homog Ideal iff is Homogeneous degree aea066f22143
-- statement:
--   The P2 M Ground Theory Heights  Heights is Homog Ideal iff is Homogeneous degree aea066f22143 construction uses the P2 M Ground Theory Heights  Heights is Homog Ideal iff is Homogeneous degree aea066f22143 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PMinimalPrimeHomog.lean#L11-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PMinimalPrimeHomog.lean#L11-L19

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PMinimalPrimeHomog
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

theorem P2M_GroundTheory_Heights__Heights_isHomogIdeal_iff_isHomogeneous_degree_aea066f22143 {R : Type*} [CommRing R] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) R)) :
    IsHomogIdeal I ↔ I.IsHomogeneous (homogeneousSubmodule (Fin n) R) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«isHomogIdeal_iff_isHomogeneous_degree» := P2M_GroundTheory_Heights__Heights_isHomogIdeal_iff_isHomogeneous_degree_aea066f22143
