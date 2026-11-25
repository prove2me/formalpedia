-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_GraphAreaHolomorphic_norm_sq_sumElim__50d1eec34ce7
-- name    : P2M_GroundTheory_Heights__Heights_GraphAreaHolomorphic_norm_sq_sumElim__50d1eec34ce7
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:18:34.984075+00:00
-- url     : https://prove2.me/theorems/e2ce675c-b67b-4c6b-8a08-022ae2f72a35
-- title:
--   P2 M Ground Theory Heights  Heights Graph Area Holomorphic norm sq sum Elim  50d1eec34ce7: P2 M Ground Theory Heights  Heights Graph Area Holomorphic norm sq sum Elim  50d1eec34ce7
-- statement:
--   The P2 M Ground Theory Heights  Heights Graph Area Holomorphic norm sq sum Elim  50d1eec34ce7 construction uses the P2 M Ground Theory Heights  Heights Graph Area Holomorphic norm sq sum Elim  50d1eec34ce7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGraphAreaHolomorphic.lean#L27-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGraphAreaHolomorphic.lean#L27-L31

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsArea
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAreaMultiplicity
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGraphAreaHolomorphic
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGraphAreaHolomorphic
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
open MeasureTheory Module
open scoped ENNReal
noncomputable section
open GroundTheory.Heights₂.Heights.GraphAreaHolomorphic

theorem P2M_GroundTheory_Heights__Heights_GraphAreaHolomorphic_norm_sq_sumElim__50d1eec34ce7 {𝕜 : Type*} [RCLike 𝕜] {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a : EuclideanSpace 𝕜 ι) (b : EuclideanSpace 𝕜 κ) :
    ‖(WithLp.toLp 2 (Sum.elim (fun i => a i) (fun i => b i)) : EuclideanSpace 𝕜 (ι ⊕ κ))‖ ^ 2 =
      ‖a‖ ^ 2 + ‖b‖ ^ 2 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«GraphAreaHolomorphic».«norm_sq_sumElim'» := P2M_GroundTheory_Heights__Heights_GraphAreaHolomorphic_norm_sq_sumElim__50d1eec34ce7
