-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SectionChowHeight_logMean_C_b565892ccd64
-- name    : P2M_GroundTheory_Heights__Heights_SectionChowHeight_logMean_C_b565892ccd64
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:38:22.812347+00:00
-- url     : https://prove2.me/theorems/93fb4f6c-4c30-42ff-b8f2-0a8cf1e4724d
-- title:
--   P2 M Ground Theory Heights  Heights Section Chow Height log Mean C b565892ccd64: P2 M Ground Theory Heights  Heights Section Chow Height log Mean C b565892ccd64
-- statement:
--   The P2 M Ground Theory Heights  Heights Section Chow Height log Mean C b565892ccd64 construction uses the P2 M Ground Theory Heights  Heights Section Chow Height log Mean C b565892ccd64 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PSectionChowHeight.lean#L19-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PSectionChowHeight.lean#L19-L25

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

theorem P2M_GroundTheory_Heights__Heights_SectionChowHeight_logMean_C_b565892ccd64 (S : Matrix (Fin n) (Fin n) ℂ) (hS : IsUnit S) (k : ℕ) (z : ℂ) :
    ReciprocityTheory.ChartRestriction.G.Geo.logMean (IndefiniteRowSideFullHecke.ArithBezout.formSphereLaw S (k + 1))
      (C z : MvPolynomial (Fin (k + 1) × Fin n) ℂ) = Real.log ‖z‖ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SectionChowHeight».«logMean_C» := P2M_GroundTheory_Heights__Heights_SectionChowHeight_logMean_C_b565892ccd64
