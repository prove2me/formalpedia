-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Cech_H_subsingleton_cacced5683ed
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_Cech_H_subsingleton_cacced5683ed
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T07:53:35.287868+00:00
-- url     : https://prove2.me/theorems/ba30da71-7f30-418c-aab8-0e617e32621b
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Cech H subsingleton cacced5683ed: P2 M Ground Theory Heights  Heights Kleiman Cech H subsingleton cacced5683ed
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Cech H subsingleton cacced5683ed construction uses the P2 M Ground Theory Heights  Heights Kleiman Cech H subsingleton cacced5683ed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PStepTwoReduce.lean#L15-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PStepTwoReduce.lean#L15-L24

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StepTwoFiltSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_QuotTransSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StepTwoPieceSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PStepTwoReduce
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u v w

theorem P2M_GroundTheory_Heights__Heights_Kleiman_Cech_H_subsingleton_cacced5683ed {n : ℕ} {U : Finset (Fin n)} {R : Type u} [CommRing R] {G : Cell U → Type v}
    [∀ I, AddCommGroup (G I)] [∀ I, Module R (G I)] (ρ : ∀ I J : Cell U, I.1 ⊆ J.1 → G I →ₗ[R] G J)
    (h : ∀ I, Subsingleton (G I)) (i : ℕ) : Subsingleton (Cech.H G ρ i) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«Cech».«H_subsingleton» := P2M_GroundTheory_Heights__Heights_Kleiman_Cech_H_subsingleton_cacced5683ed
