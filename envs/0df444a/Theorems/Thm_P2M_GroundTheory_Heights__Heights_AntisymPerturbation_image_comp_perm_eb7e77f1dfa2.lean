-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_AntisymPerturbation_image_comp_perm_eb7e77f1dfa2
-- name    : P2M_GroundTheory_Heights__Heights_AntisymPerturbation_image_comp_perm_eb7e77f1dfa2
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T00:15:26.08446+00:00
-- url     : https://prove2.me/theorems/a8bde11d-5006-4186-9f66-9d93cbdb1c55
-- title:
--   P2 M Ground Theory Heights  Heights Antisym Perturbation image comp perm eb7e77f1dfa2: P2 M Ground Theory Heights  Heights Antisym Perturbation image comp perm eb7e77f1dfa2
-- statement:
--   The P2 M Ground Theory Heights  Heights Antisym Perturbation image comp perm eb7e77f1dfa2 construction uses the P2 M Ground Theory Heights  Heights Antisym Perturbation image comp perm eb7e77f1dfa2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PAntisymPerturbation.lean#L65-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PAntisymPerturbation.lean#L65-L95

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

theorem P2M_GroundTheory_Heights__Heights_AntisymPerturbation_image_comp_perm_eb7e77f1dfa2 (σ : Equiv.Perm (T × Fin N)) (τ : T) {a b a' b' : Fin N}
    (hσa : σ (τ, a) = (τ, a')) (hσb : σ (τ, b) = (τ, b')) {K : Set (T × Fin N → ℝ)}
    (hKc : IsCompact K) (hKH : K ⊆ diagHyperplane T N τ a' b')
    (hKO : ∃ O : Set (T × Fin N → ℝ), IsOpen O ∧ (O ∩ diagHyperplane T N τ a' b').Nonempty ∧
      O ∩ diagHyperplane T N τ a' b' ⊆ K) :
    IsCompact ((fun y => y ∘ ⇑σ) '' K) ∧ (fun y => y ∘ ⇑σ) '' K ⊆ diagHyperplane T N τ a b ∧
      ∃ O : Set (T × Fin N → ℝ), IsOpen O ∧ (O ∩ diagHyperplane T N τ a b).Nonempty ∧
        O ∩ diagHyperplane T N τ a b ⊆ (fun y => y ∘ ⇑σ) '' K := by sorry

alias «GroundTheory».«Heights₂».«Heights».«AntisymPerturbation».«image_comp_perm» := P2M_GroundTheory_Heights__Heights_AntisymPerturbation_image_comp_perm_eb7e77f1dfa2
