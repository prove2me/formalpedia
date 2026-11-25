-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SectionChowHeight_chowHeight_C_986af5068273
-- name    : P2M_GroundTheory_Heights__Heights_SectionChowHeight_chowHeight_C_986af5068273
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:38:10.41078+00:00
-- url     : https://prove2.me/theorems/d06e3540-d6a7-4e8d-b749-0d44f7809e33
-- title:
--   P2 M Ground Theory Heights  Heights Section Chow Height chow Height C 986af5068273: P2 M Ground Theory Heights  Heights Section Chow Height chow Height C 986af5068273
-- statement:
--   The P2 M Ground Theory Heights  Heights Section Chow Height chow Height C 986af5068273 construction uses the P2 M Ground Theory Heights  Heights Section Chow Height chow Height C 986af5068273 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PSectionChowHeight.lean#L27-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PSectionChowHeight.lean#L27-L41

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

theorem P2M_GroundTheory_Heights__Heights_SectionChowHeight_chowHeight_C_986af5068273 (S : Matrix (Fin n) (Fin n) ℂ) (hS : IsUnit S) (e : ℕ) {a : ℚ} (ha : a ≠ 0) :
    IndefiniteRowSideFullHecke.ArithBezout.chowHeight S (C a : MvPolynomial (Fin (e + 1) × Fin n) ℚ) 0 = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SectionChowHeight».«chowHeight_C» := P2M_GroundTheory_Heights__Heights_SectionChowHeight_chowHeight_C_986af5068273
