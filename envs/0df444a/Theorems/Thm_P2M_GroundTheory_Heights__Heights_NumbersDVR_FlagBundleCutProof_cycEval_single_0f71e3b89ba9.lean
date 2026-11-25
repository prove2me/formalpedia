-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleCutProof_cycEval_single_0f71e3b89ba9
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleCutProof_cycEval_single_0f71e3b89ba9
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:29:48.932746+00:00
-- url     : https://prove2.me/theorems/8e9832e8-2b73-469c-bd8d-26e1526a27c7
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Flag Bundle Cut Proof cyc Eval single 0f71e3b89ba9: P2 M Ground Theory Heights  Heights Numbers DVR Flag Bundle Cut Proof cyc Eval single 0f71e3b89ba9
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Flag Bundle Cut Proof cyc Eval single 0f71e3b89ba9 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Flag Bundle Cut Proof cyc Eval single 0f71e3b89ba9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFlagBundleCut.lean#L27-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFlagBundleCut.lean#L27-L33

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsFlagBundleForms
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsFlagBundleSectionDiv
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PIntNumSymm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFlagBundleCut
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
open GroundTheory.Heights₂.Heights.NumbersDVR.FlagBundleCutProof

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleCutProof_cycEval_single_0f71e3b89ba9 {K : Type} {ι : K → Type} {F : Type} [Field F]
    (n : Ideal (MRing ι F) → ℤ) (Z : Ideal (MRing ι F)) :
    cycEval n (fun W => by classical exact if W = Z then 1 else 0) = n Z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«FlagBundleCutProof».«cycEval_single» := P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleCutProof_cycEval_single_0f71e3b89ba9
