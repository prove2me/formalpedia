-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SectionChowHeight_chowHeight_C_mul_cycle_25bc873a45af
-- name    : P2M_GroundTheory_Heights__Heights_SectionChowHeight_chowHeight_C_mul_cycle_25bc873a45af
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:40:44.396148+00:00
-- url     : https://prove2.me/theorems/9434ed73-638f-50d1-8a9e-db11b244171a
-- title:
--   P2 M Ground Theory Heights  Heights Section Chow Height chow Height C mul cycle 25bc873a45af: P2 M Ground Theory Heights  Heights Section Chow Height chow Height C mul cycle 25bc873a45af
-- statement:
--   The P2 M Ground Theory Heights  Heights Section Chow Height chow Height C mul cycle 25bc873a45af construction uses the P2 M Ground Theory Heights  Heights Section Chow Height chow Height C mul cycle 25bc873a45af property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PSectionChowHeight.lean#L43-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PSectionChowHeight.lean#L43-L60

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsSectionChowHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PRecQOfRecursion
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ArchOfPlacesEmbedding
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ContinuousHermNormGroup
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PSectionChowHeight
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
open MvPolynomial NumberField
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar IsHorizontal divSupp multAt)
open GroundTheory.Heights₂.Heights.SectionChowHeight
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_SectionChowHeight_chowHeight_C_mul_cycle_25bc873a45af (S : Matrix (Fin n) (Fin n) ℂ) (hS : IsUnit S) {e : ℕ} {ι : Type}
    (Z : ι →₀ ℕ) (g : ι → MvPolynomial (Fin (e + 1) × Fin n) ℚ) (d : ι → ℕ)
    (hg : ∀ i ∈ Z.support, g i ≠ 0) {a : ℚ} (ha : a ≠ 0) :
    IndefiniteRowSideFullHecke.ArithBezout.chowHeight S (C a * ∏ i ∈ Z.support, g i ^ Z i) (∑ i ∈ Z.support, Z i * d i) =
      ∑ i ∈ Z.support, (Z i : ℝ) * IndefiniteRowSideFullHecke.ArithBezout.chowHeight S (g i) (d i) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SectionChowHeight».«chowHeight_C_mul_cycle» := P2M_GroundTheory_Heights__Heights_SectionChowHeight_chowHeight_C_mul_cycle_25bc873a45af
