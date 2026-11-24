-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_AntisymPerturbation_rename_mul_eq_or_neg_9d0bf095579c
-- name    : P2M_GroundTheory_Heights__Heights_AntisymPerturbation_rename_mul_eq_or_neg_9d0bf095579c
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:19:43.414806+00:00
-- url     : https://prove2.me/theorems/93186270-f2bb-47bf-8025-b1aaa0fe58ce
-- title:
--   P2 M Ground Theory Heights  Heights Antisym Perturbation rename mul eq or neg 9d0bf095579c: P2 M Ground Theory Heights  Heights Antisym Perturbation rename mul eq or neg 9d0bf095579c
-- statement:
--   The P2 M Ground Theory Heights  Heights Antisym Perturbation rename mul eq or neg 9d0bf095579c construction uses the P2 M Ground Theory Heights  Heights Antisym Perturbation rename mul eq or neg 9d0bf095579c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PAntisymPerturbation.lean#L17-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PAntisymPerturbation.lean#L17-L26

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PAntisymPerturbation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
open GroundTheory.Heights₂.Heights.AntisymPerturbation
variable {T : Type} [Fintype T] [DecidableEq T] {N j : ℕ}
omit [Fintype T] [DecidableEq T]

theorem P2M_GroundTheory_Heights__Heights_AntisymPerturbation_rename_mul_eq_or_neg_9d0bf095579c {R : MvPolynomial (T × Fin N) ℝ} {σ ρ : Equiv.Perm (T × Fin N)}
    (hσ : rename σ R = R ∨ rename σ R = -R) (hρ : rename ρ R = R ∨ rename ρ R = -R) :
    rename ⇑(σ * ρ) R = R ∨ rename ⇑(σ * ρ) R = -R := by sorry

alias «GroundTheory».«Heights₂».«Heights».«AntisymPerturbation».«rename_mul_eq_or_neg» := P2M_GroundTheory_Heights__Heights_AntisymPerturbation_rename_mul_eq_or_neg_9d0bf095579c
