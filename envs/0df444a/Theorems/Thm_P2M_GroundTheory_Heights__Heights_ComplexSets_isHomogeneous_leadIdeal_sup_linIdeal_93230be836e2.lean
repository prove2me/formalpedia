-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_isHomogeneous_leadIdeal_sup_linIdeal_93230be836e2
-- name    : P2M_GroundTheory_Heights__Heights_ComplexSets_isHomogeneous_leadIdeal_sup_linIdeal_93230be836e2
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:16:32.910231+00:00
-- url     : https://prove2.me/theorems/7940ec69-1dd8-4fa5-ae40-4630708b992b
-- title:
--   P2 M Ground Theory Heights  Heights Complex Sets is Homogeneous lead Ideal sup lin Ideal 93230be836e2: P2 M Ground Theory Heights  Heights Complex Sets is Homogeneous lead Ideal sup lin Ideal 93230be8
-- statement:
--   The P2 M Ground Theory Heights  Heights Complex Sets is Homogeneous lead Ideal sup lin Ideal 93230be836e2 construction uses the P2 M Ground Theory Heights  Heights Complex Sets is Homogeneous lead Ideal sup lin Ideal 93230be836e2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PConeAvoidsOpen.lean#L15-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PConeAvoidsOpen.lean#L15-L23

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StConeAvoidsOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PConeAvoidsOpen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.ComplexSets
open MvPolynomial
noncomputable section
attribute [local instance] MvPolynomial.gradedAlgebra
variable {n d : ℕ}

theorem P2M_GroundTheory_Heights__Heights_ComplexSets_isHomogeneous_leadIdeal_sup_linIdeal_93230be836e2 (J : Ideal (MvPolynomial (Fin n) ℂ))
    (A : Matrix (Fin d) (Fin n) ℂ) :
    (leadIdeal J ⊔ linIdeal A).IsHomogeneous (homogeneousSubmodule (Fin n) ℂ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ComplexSets».«isHomogeneous_leadIdeal_sup_linIdeal» := P2M_GroundTheory_Heights__Heights_ComplexSets_isHomogeneous_leadIdeal_sup_linIdeal_93230be836e2
