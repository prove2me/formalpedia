-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_AntisymPerturbation_rename_swap_eq_or_neg_9ae4b8a333fd
-- name    : P2M_GroundTheory_Heights__Heights_AntisymPerturbation_rename_swap_eq_or_neg_9ae4b8a333fd
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T00:15:30.608911+00:00
-- url     : https://prove2.me/theorems/65153d55-087d-4f40-8086-1b835df23562
-- title:
--   P2 M Ground Theory Heights  Heights Antisym Perturbation rename swap eq or neg 9ae4b8a333fd: P2 M Ground Theory Heights  Heights Antisym Perturbation rename swap eq or neg 9ae4b8a333fd
-- statement:
--   The P2 M Ground Theory Heights  Heights Antisym Perturbation rename swap eq or neg 9ae4b8a333fd construction uses the P2 M Ground Theory Heights  Heights Antisym Perturbation rename swap eq or neg 9ae4b8a333fd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PAntisymPerturbation.lean#L28-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PAntisymPerturbation.lean#L28-L61

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

theorem P2M_GroundTheory_Heights__Heights_AntisymPerturbation_rename_swap_eq_or_neg_9ae4b8a333fd {R : MvPolynomial (T × Fin N) ℝ} (hR : R ∈ antisymSpace T N j)
    (τ : T) (a c : Fin N) (hac : a.val ≤ c.val) (hblk : c.val < j ∨ j ≤ a.val) :
    rename ⇑(Equiv.swap (τ, a) (τ, c)) R = R ∨ rename ⇑(Equiv.swap (τ, a) (τ, c)) R = -R := by sorry

alias «GroundTheory».«Heights₂».«Heights».«AntisymPerturbation».«rename_swap_eq_or_neg» := P2M_GroundTheory_Heights__Heights_AntisymPerturbation_rename_swap_eq_or_neg_9ae4b8a333fd
