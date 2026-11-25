-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_SerreGraded_torsion_bound_7e4614d2b7b2
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_SerreGraded_torsion_bound_7e4614d2b7b2
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:18:50.633543+00:00
-- url     : https://prove2.me/theorems/4ca8754c-c16c-4896-a172-f6f5a3d70eda
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Serre Graded torsion bound 7e4614d2b7b2: P2 M Ground Theory Heights  Heights Hilbert Samuel Serre Graded torsion bound 7e4614d2b7b2
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Serre Graded torsion bound 7e4614d2b7b2 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Serre Graded torsion bound 7e4614d2b7b2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PSerreGraded.lean#L158-L245
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PSerreGraded.lean#L158-L245

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsSerreGraded
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PSerreGraded
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
noncomputable section
open GroundTheory.Heights₂.Heights.HilbertSamuel.SerreGraded
open Polynomial
variable {Ω : Type} [Field Ω] {q r : ℕ} (w : Fin q → Ω) (d : Fin r → ℕ) (t : Fin r → Ω)
variable [Algebra (MvPolynomial (Fin q) ℤ) (Polynomial Ω)]

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_SerreGraded_torsion_bound_7e4614d2b7b2 (hA : algebraMap (MvPolynomial (Fin q) ℤ) (Polynomial Ω) = act w) (u : Fin q) :
    ∃ E : ℕ, ∀ m ∈ gradedModule q d t,
      (∀ j, w j ≠ 0 → ∃ D : ℕ,
        (MvPolynomial.X j ^ D : MvPolynomial (Fin q) ℤ) • m ∈ shifted w d t u) →
      ∀ k, E ≤ k → ∃ z ∈ gradedSpan w d t k, m.coeff (k + 1) = w u * z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«SerreGraded».«torsion_bound» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_SerreGraded_torsion_bound_7e4614d2b7b2
