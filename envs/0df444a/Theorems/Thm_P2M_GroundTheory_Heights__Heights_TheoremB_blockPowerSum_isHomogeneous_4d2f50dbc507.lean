-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_TheoremB_blockPowerSum_isHomogeneous_4d2f50dbc507
-- name    : P2M_GroundTheory_Heights__Heights_TheoremB_blockPowerSum_isHomogeneous_4d2f50dbc507
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:41:05.789213+00:00
-- url     : https://prove2.me/theorems/399be1e7-56f6-4ad5-9d2c-d88d3032fc86
-- title:
--   P2 M Ground Theory Heights  Heights Theorem B block Power Sum is Homogeneous 4d2f50dbc507: P2 M Ground Theory Heights  Heights Theorem B block Power Sum is Homogeneous 4d2f50dbc507
-- statement:
--   The P2 M Ground Theory Heights  Heights Theorem B block Power Sum is Homogeneous 4d2f50dbc507 construction uses the P2 M Ground Theory Heights  Heights Theorem B block Power Sum is Homogeneous 4d2f50dbc507 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MultinomialWeights/Statements.lean#L290-L293
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MultinomialWeights/Statements.lean#L290-L293

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_FlagBasic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MultinomialWeights_Statements
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.TheoremB
open MvPolynomial Finset
variable (d : IndexData)

theorem P2M_GroundTheory_Heights__Heights_TheoremB_blockPowerSum_isHomogeneous_4d2f50dbc507 (f N k : ℕ) (τ : Fin f) :
    (RestTerms.blockPowerSum f N k τ).IsHomogeneous k := by sorry

alias «GroundTheory».«Heights₂».«Heights».«TheoremB».«blockPowerSum_isHomogeneous» := P2M_GroundTheory_Heights__Heights_TheoremB_blockPowerSum_isHomogeneous_4d2f50dbc507
