-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_joinClosureDeg_natAdd_18bace97db63
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_joinClosureDeg_natAdd_18bace97db63
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:11:57.177668+00:00
-- url     : https://prove2.me/theorems/3e015f77-7a8a-4a28-a371-13a3d55fcb12
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR join Closure Deg nat Add 18bace97db63: P2 M Ground Theory Heights  Heights Numbers DVR join Closure Deg nat Add 18bace97db63
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR join Closure Deg nat Add 18bace97db63 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR join Closure Deg nat Add 18bace97db63 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PSegreFlagClosurePullback.lean#L84-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PSegreFlagClosurePullback.lean#L84-L87

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_joinClosureDeg_natAdd_18bace97db63 (ζ : Option (Option K) → ℤ) (L : Fin m → K → ℤ) :
    joinClosureDeg ζ L ∘ Fin.natAdd 1 = fun j => joinDeg (L j) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«joinClosureDeg_natAdd» := P2M_GroundTheory_Heights__Heights_NumbersDVR_joinClosureDeg_natAdd_18bace97db63
