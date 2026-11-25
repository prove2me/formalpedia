-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_rename_closureForm_d4ffbeabd6a1
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_rename_closureForm_d4ffbeabd6a1
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:12:18.475624+00:00
-- url     : https://prove2.me/theorems/71111bfe-65d1-4a25-af4b-92dba909efa5
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR rename closure Form d4ffbeabd6a1: P2 M Ground Theory Heights  Heights Numbers DVR rename closure Form d4ffbeabd6a1
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR rename closure Form d4ffbeabd6a1 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR rename closure Form d4ffbeabd6a1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PSegreFlagClosurePullback.lean#L89-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PSegreFlagClosurePullback.lean#L89-L97

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsSegreFlagClosure
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsFlagIndependence
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsPairNumberRelabel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsVerticalDivisorJoinPullback
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsSegreFlagClosureBirational
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFlagIndependenceAlgebra
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSegreFlagClosurePullback
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
variable {K : Type} {ι : K → Type} {m : ℕ}

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_rename_closureForm_d4ffbeabd6a1 {R : Type*} [CommRing R] (M M' : ℕ) (h : MRing (bundleIdx (bundleIdx ι M) M') R)
    (F : Fin m → MRing ι R) :
    (fun i => rename (closureVarEquiv ι M M') (closureForm M M' h F i)) =
      joinClosureForm M M' (rename (closureVarEquiv ι M M') h) F := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«rename_closureForm» := P2M_GroundTheory_Heights__Heights_NumbersDVR_rename_closureForm_d4ffbeabd6a1
