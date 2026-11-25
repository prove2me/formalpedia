-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_NumericalSegre_proof_cb3426470abf
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_NumericalSegre_proof_cb3426470abf
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T13:33:19.879062+00:00
-- url     : https://prove2.me/theorems/5a9b9801-366c-4e2f-8018-32c8d368ab05
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Numerical Segre proof cb3426470abf: P2 M Ground Theory Heights  Heights Numbers DVR Numerical Segre proof cb3426470abf
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Numerical Segre proof cb3426470abf construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Numerical Segre proof cb3426470abf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PNumericalSegre.lean#L182-L229
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PNumericalSegre.lean#L182-L229

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsFlagBundle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PIntNumSymm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PNumericalSegre
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_IntNumSymm_proof_70e6ef43d2f0

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
open NumericalSegreProof

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_NumericalSegre_proof_cb3426470abf (hadd : FieldNumbers.IntNumAdd.Statement.{0})
    (hdim : FlagBundleDim.Statement) (hcut : FlagBundleCut.Statement)
    (hvan : FlagBundlePullbackVanish.Statement) (hbase : FlagBundleLineBase.Statement) :
    NumericalSegre.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«NumericalSegre».«proof» := P2M_GroundTheory_Heights__Heights_NumbersDVR_NumericalSegre_proof_cb3426470abf
