-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocRingDimLe_valIn_change_9fd10f331b07
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocRingDimLe_valIn_change_9fd10f331b07
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:08:33.543359+00:00
-- url     : https://prove2.me/theorems/b8a521bc-ddc4-4c51-9c62-9996f8b36b6e
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Hom Loc Ring Dim Le val In change 9fd10f331b07: P2 M Ground Theory Heights  Heights Numbers DVR Hom Loc Ring Dim Le val In change 9fd10f331b07
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Hom Loc Ring Dim Le val In change 9fd10f331b07 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Hom Loc Ring Dim Le val In change 9fd10f331b07 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PHomLocRingDimLe.lean#L68-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PHomLocRingDimLe.lean#L68-L74

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsHomLocRingLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PHomLocRingLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMultiHomogPrimeCriterion
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PHomLocRingDimLe
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
universe u
open GroundTheory.Heights₂.Heights.NumbersDVR.HomLocRingDimLe
variable {R : Type u} [CommRing R] {K : Type} [DecidableEq K] {ι : K → Type}
variable (P W : Ideal (MRing ι R)) [P.IsPrime]
variable {P W}

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocRingDimLe_valIn_change_9fd10f331b07 (hPW : P ≤ W) {q : Ideal (homLocRing P W)} {b : K → ℕ} {f g g' : MRing ι R}
    (hg : IsMultiHomog g b) (hg' : IsMultiHomog g' b) (hgW : g ∉ W) (hg'W : g' ∉ W)
    (h : ValIn P W q (frac P f / frac P g)) : ValIn P W q (frac P f / frac P g') := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«HomLocRingDimLe».«valIn_change» := P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocRingDimLe_valIn_change_9fd10f331b07
