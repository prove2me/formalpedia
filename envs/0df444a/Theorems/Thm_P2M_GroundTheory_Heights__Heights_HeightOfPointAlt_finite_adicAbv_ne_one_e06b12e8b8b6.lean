-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HeightOfPointAlt_finite_adicAbv_ne_one_e06b12e8b8b6
-- name    : P2M_GroundTheory_Heights__Heights_HeightOfPointAlt_finite_adicAbv_ne_one_e06b12e8b8b6
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:19:07.514426+00:00
-- url     : https://prove2.me/theorems/6b745329-a0d5-4ab4-a4ab-40dcee0b9e65
-- title:
--   P2 M Ground Theory Heights  Heights Height Of Point Alt finite adic Abv ne one e06b12e8b8b6: P2 M Ground Theory Heights  Heights Height Of Point Alt finite adic Abv ne one e06b12e8b8b6
-- statement:
--   The P2 M Ground Theory Heights  Heights Height Of Point Alt finite adic Abv ne one e06b12e8b8b6 construction uses the P2 M Ground Theory Heights  Heights Height Of Point Alt finite adic Abv ne one e06b12e8b8b6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PHeightOfPoint.lean#L29-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PHeightOfPoint.lean#L29-L38

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

theorem P2M_GroundTheory_Heights__Heights_HeightOfPointAlt_finite_adicAbv_ne_one_e06b12e8b8b6 {c : K} (hc : c ≠ 0) :
    {v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) |
      NumberField.HeightOneSpectrum.adicAbv K v c ≠ 1}.Finite := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HeightOfPointAlt».«finite_adicAbv_ne_one» := P2M_GroundTheory_Heights__Heights_HeightOfPointAlt_finite_adicAbv_ne_one_e06b12e8b8b6
