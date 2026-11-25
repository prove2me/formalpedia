-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_joinClosureDeg_comp_5064ccd76e47
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_joinClosureDeg_comp_5064ccd76e47
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:12:03.443532+00:00
-- url     : https://prove2.me/theorems/192a5773-0c12-493d-9f89-5f40c69f6af3
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR join Closure Deg comp 5064ccd76e47: P2 M Ground Theory Heights  Heights Numbers DVR join Closure Deg comp 5064ccd76e47
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR join Closure Deg comp 5064ccd76e47 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR join Closure Deg comp 5064ccd76e47 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PSegreFlagClosurePullback.lean#L74-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PSegreFlagClosurePullback.lean#L74-L82

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_joinClosureDeg_comp_5064ccd76e47 (ζ : Option (Option K) → ℤ) (L : Fin m → K → ℤ) :
    (fun i => joinClosureDeg ζ L i ∘ closureBlockEquiv K) = closureDeg ζ L := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«joinClosureDeg_comp» := P2M_GroundTheory_Heights__Heights_NumbersDVR_joinClosureDeg_comp_5064ccd76e47
