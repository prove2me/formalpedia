-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_joinClosureForm_natAdd_7163a214e1b9
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_joinClosureForm_natAdd_7163a214e1b9
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:12:08.502028+00:00
-- url     : https://prove2.me/theorems/bc1f1467-62c9-42ed-b382-2a8d8b131aa4
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR join Closure Form nat Add 7163a214e1b9: P2 M Ground Theory Heights  Heights Numbers DVR join Closure Form nat Add 7163a214e1b9
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR join Closure Form nat Add 7163a214e1b9 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR join Closure Form nat Add 7163a214e1b9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PSegreFlagClosurePullback.lean#L99-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PSegreFlagClosurePullback.lean#L99-L102

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_joinClosureForm_natAdd_7163a214e1b9 {R : Type*} [CommRing R] (M M' : ℕ) (h : MRing (Sum.elim ι (lineBlocks M M')) R)
    (F : Fin m → MRing ι R) : joinClosureForm M M' h F ∘ Fin.natAdd 1 = fun j => joinForm (F j) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«joinClosureForm_natAdd» := P2M_GroundTheory_Heights__Heights_NumbersDVR_joinClosureForm_natAdd_7163a214e1b9
