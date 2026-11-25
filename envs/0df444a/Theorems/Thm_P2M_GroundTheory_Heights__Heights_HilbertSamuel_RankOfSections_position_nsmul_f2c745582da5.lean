-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_RankOfSections_position_nsmul_f2c745582da5
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_RankOfSections_position_nsmul_f2c745582da5
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:19:15.892377+00:00
-- url     : https://prove2.me/theorems/a6832b12-f2c6-46fc-a84e-ae780711f6fe
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Rank Of Sections position nsmul f2c745582da5: P2 M Ground Theory Heights  Heights Hilbert Samuel Rank Of Sections position nsmul f2c745582da5
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Rank Of Sections position nsmul f2c745582da5 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Rank Of Sections position nsmul f2c745582da5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PRankOfSections.lean#L13-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PRankOfSections.lean#L13-L27

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsHilbert
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PRankOfSections
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
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
open GroundTheory.Heights₂.Heights.HilbertSamuel.RankOfSections

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_RankOfSections_position_nsmul_f2c745582da5 {d : ℕ} {A : Type*} [AddCommGroup A] (f : (Fin d → A) → ℤ)
    (hf : ∀ (bs : Fin d → A) (j : Fin d) (x y : A),
      f (Function.update bs j (x + y)) = f (Function.update bs j x) + f (Function.update bs j y))
    (bs : Fin d → A) (j : Fin d) (m : ℕ) (y : A) :
    f (Function.update bs j (m • y)) = (m : ℤ) * f (Function.update bs j y) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«RankOfSections».«position_nsmul» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_RankOfSections_position_nsmul_f2c745582da5
