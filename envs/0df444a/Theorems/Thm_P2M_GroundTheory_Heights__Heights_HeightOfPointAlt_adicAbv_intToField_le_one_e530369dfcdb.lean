-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HeightOfPointAlt_adicAbv_intToField_le_one_e530369dfcdb
-- name    : P2M_GroundTheory_Heights__Heights_HeightOfPointAlt_adicAbv_intToField_le_one_e530369dfcdb
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:20:47.156505+00:00
-- url     : https://prove2.me/theorems/07b3172d-a03a-5697-b0f3-470e7c72ac1e
-- title:
--   P2 M Ground Theory Heights  Heights Height Of Point Alt adic Abv int To Field le one e530369dfcdb: P2 M Ground Theory Heights  Heights Height Of Point Alt adic Abv int To Field le one e530369dfcdb
-- statement:
--   The P2 M Ground Theory Heights  Heights Height Of Point Alt adic Abv int To Field le one e530369dfcdb construction uses the P2 M Ground Theory Heights  Heights Height Of Point Alt adic Abv int To Field le one e530369dfcdb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PHeightOfPoint.lean#L44-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PHeightOfPoint.lean#L44-L49

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_IsProbabilityMeasureSphereLaw
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ContinuousHermNormGroup
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PHeightOfPoint
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial NumberField ComplexAt TensorProduct
noncomputable section
open GroundTheory.Heights₂.Heights.HeightOfPointAlt
variable {K : Type*} [Field K] [NumberField K]
variable {F : Type*} [Field F] [NumberField F] [Algebra F K]
omit [NumberField F]

theorem P2M_GroundTheory_Heights__Heights_HeightOfPointAlt_adicAbv_intToField_le_one_e530369dfcdb (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (a : 𝓞 F) :
    NumberField.HeightOneSpectrum.adicAbv K v (intToField F K a) ≤ 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HeightOfPointAlt».«adicAbv_intToField_le_one» := P2M_GroundTheory_Heights__Heights_HeightOfPointAlt_adicAbv_intToField_le_one_e530369dfcdb
