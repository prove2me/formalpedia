-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_PairNumberRelabel_foldr_diffStep_perm_e8f8d5ef2204
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_PairNumberRelabel_foldr_diffStep_perm_e8f8d5ef2204
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:00:48.338358+00:00
-- url     : https://prove2.me/theorems/b324b0d0-f362-572a-8ab2-06abda3b4fe7
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Pair Number Relabel foldr diff Step perm e8f8d5ef2204: P2 M Ground Theory Heights  Heights Numbers DVR Pair Number Relabel foldr diff Step perm e8f8d5ef
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Pair Number Relabel foldr diff Step perm e8f8d5ef2204 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Pair Number Relabel foldr diff Step perm e8f8d5ef2204 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPairNumberRelabel.lean#L120-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPairNumberRelabel.lean#L120-L126

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsPairNumberRelabel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_IntNumRelabel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PRenameMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PRenameMultiProjPrime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PExistsUniqueRelabel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PPairNumberRelabel
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
open GroundTheory.Heights₂.Heights.NumbersDVR.PairNumberRelabel
variable {K : Type*} [DecidableEq K] {ι : K → Type*}
omit [DecidableEq K]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_PairNumberRelabel_foldr_diffStep_perm_e8f8d5ef2204 {l₁ l₂ : List (K → ℤ)} (p : l₁.Perm l₂) (h : (K → ℤ) → ℤ) :
    l₁.foldr diffStep h = l₂.foldr diffStep h := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«PairNumberRelabel».«foldr_diffStep_perm» := P2M_GroundTheory_Heights__Heights_NumbersDVR_PairNumberRelabel_foldr_diffStep_perm_e8f8d5ef2204
