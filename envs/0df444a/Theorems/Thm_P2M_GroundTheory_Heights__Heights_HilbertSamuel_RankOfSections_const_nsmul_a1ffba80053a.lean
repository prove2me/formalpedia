-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_RankOfSections_const_nsmul_a1ffba80053a
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_RankOfSections_const_nsmul_a1ffba80053a
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:23:34.682437+00:00
-- url     : https://prove2.me/theorems/59bec1a0-ee63-4159-a5a2-6a8548e58576
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Rank Of Sections const nsmul a1ffba80053a: P2 M Ground Theory Heights  Heights Hilbert Samuel Rank Of Sections const nsmul a1ffba80053a
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Rank Of Sections const nsmul a1ffba80053a construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Rank Of Sections const nsmul a1ffba80053a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PRankOfSections.lean#L29-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PRankOfSections.lean#L29-L57

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

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_RankOfSections_const_nsmul_a1ffba80053a {d : ℕ} {A : Type*} [AddCommGroup A] (f : (Fin d → A) → ℤ)
    (hf : ∀ (bs : Fin d → A) (j : Fin d) (x y : A),
      f (Function.update bs j (x + y)) = f (Function.update bs j x) + f (Function.update bs j y))
    (n : ℕ) (x : A) :
    f (fun _ => n • x) = (n : ℤ) ^ d * f (fun _ => x) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«RankOfSections».«const_nsmul» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_RankOfSections_const_nsmul_a1ffba80053a
