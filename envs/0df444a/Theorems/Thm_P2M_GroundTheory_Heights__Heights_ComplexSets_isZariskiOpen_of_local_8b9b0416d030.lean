-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_isZariskiOpen_of_local_8b9b0416d030
-- name    : P2M_GroundTheory_Heights__Heights_ComplexSets_isZariskiOpen_of_local_8b9b0416d030
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:16:14.532598+00:00
-- url     : https://prove2.me/theorems/487f8726-2cae-4c3b-a4f8-1fc599888850
-- title:
--   P2 M Ground Theory Heights  Heights Complex Sets is Zariski Open of local 8b9b0416d030: P2 M Ground Theory Heights  Heights Complex Sets is Zariski Open of local 8b9b0416d030
-- statement:
--   The P2 M Ground Theory Heights  Heights Complex Sets is Zariski Open of local 8b9b0416d030 construction uses the P2 M Ground Theory Heights  Heights Complex Sets is Zariski Open of local 8b9b0416d030 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PConeAvoidsOpen.lean#L52-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PConeAvoidsOpen.lean#L52-L65

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

theorem P2M_GroundTheory_Heights__Heights_ComplexSets_isZariskiOpen_of_local_8b9b0416d030 {U : Set (Matrix (Fin d) (Fin n) ℂ)}
    (H : ∀ A₀ ∈ U, ∃ p : MvPolynomial (Fin d × Fin n) ℂ,
      eval (fun ij : Fin d × Fin n => A₀ ij.1 ij.2) p ≠ 0 ∧
        ∀ A : Matrix (Fin d) (Fin n) ℂ, eval (fun ij : Fin d × Fin n => A ij.1 ij.2) p ≠ 0 → A ∈ U) :
    IsZariskiOpen U := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ComplexSets».«isZariskiOpen_of_local» := P2M_GroundTheory_Heights__Heights_ComplexSets_isZariskiOpen_of_local_8b9b0416d030
