-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_isLocalizedModule_genFibPiece_364fc6d1a2fe
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_isLocalizedModule_genFibPiece_364fc6d1a2fe
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:10:44.023404+00:00
-- url     : https://prove2.me/theorems/dc010707-ae42-4d66-9139-463f558df84b
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR is Localized Module gen Fib Piece 364fc6d1a2fe: P2 M Ground Theory Heights  Heights Numbers DVR is Localized Module gen Fib Piece 364fc6d1a2fe
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR is Localized Module gen Fib Piece 364fc6d1a2fe construction uses the P2 M Ground Theory Heights  Heights Numbers DVR is Localized Module gen Fib Piece 364fc6d1a2fe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PGenericPieceRank.lean#L55-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PGenericPieceRank.lean#L55-L115

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PGenericPieceRank
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
open MvPolynomial
noncomputable section
variable {O : Type*} [CommRing O] [IsDomain O] {K : Type*} [DecidableEq K] {ι : K → Type*}

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_isLocalizedModule_genFibPiece_364fc6d1a2fe (P : Ideal (MRing ι O)) (m : K → ℕ) :
    IsLocalizedModule (nonZeroDivisors O) (genFibPiece P m) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«isLocalizedModule_genFibPiece» := P2M_GroundTheory_Heights__Heights_NumbersDVR_isLocalizedModule_genFibPiece_364fc6d1a2fe
