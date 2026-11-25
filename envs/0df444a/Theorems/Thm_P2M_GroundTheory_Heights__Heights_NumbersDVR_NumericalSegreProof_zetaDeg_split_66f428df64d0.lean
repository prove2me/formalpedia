-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_NumericalSegreProof_zetaDeg_split_66f428df64d0
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_NumericalSegreProof_zetaDeg_split_66f428df64d0
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:16:04.349483+00:00
-- url     : https://prove2.me/theorems/64cb8b96-c614-5cc5-9e25-803364ab8805
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Numerical Segre Proof zeta Deg split 66f428df64d0: P2 M Ground Theory Heights  Heights Numbers DVR Numerical Segre Proof zeta Deg split 66f428df64d0
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Numerical Segre Proof zeta Deg split 66f428df64d0 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Numerical Segre Proof zeta Deg split 66f428df64d0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PNumericalSegre.lean#L152-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PNumericalSegre.lean#L152-L155

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsFlagBundle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PIntNumSymm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PNumericalSegre
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
open GroundTheory.Heights₂.Heights.NumbersDVR.NumericalSegreProof

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_NumericalSegreProof_zetaDeg_split_66f428df64d0 {K : Type*} (a c : K → ℤ) :
    ((zetaDeg + liftDeg (c - a)) + liftDeg (a - c) : Option K → ℤ) = zetaDeg := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«NumericalSegreProof».«zetaDeg_split» := P2M_GroundTheory_Heights__Heights_NumbersDVR_NumericalSegreProof_zetaDeg_split_66f428df64d0
