-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_YPlusSmall_exists_of_mem_secM_2a2a6c5f5bc7
-- name    : P2M_GroundTheory_Heights__Heights_YPlusSmall_exists_of_mem_secM_2a2a6c5f5bc7
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:43:54.42878+00:00
-- url     : https://prove2.me/theorems/a7de9c59-d4d9-4568-99ef-a1689e2961c1
-- title:
--   P2 M Ground Theory Heights  Heights YPlus Small exists of mem sec M 2a2a6c5f5bc7: P2 M Ground Theory Heights  Heights YPlus Small exists of mem sec M 2a2a6c5f5bc7
-- statement:
--   The P2 M Ground Theory Heights  Heights YPlus Small exists of mem sec M 2a2a6c5f5bc7 construction uses the P2 M Ground Theory Heights  Heights YPlus Small exists of mem sec M 2a2a6c5f5bc7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PYPlusSmall.lean#L48-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PYPlusSmall.lean#L48-L59

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PYPlusSmall
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G
noncomputable section
open GroundTheory.Heights₂.Heights.YPlusSmall
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

theorem P2M_GroundTheory_Heights__Heights_YPlusSmall_exists_of_mem_secM_2a2a6c5f5bc7 {κ : Type} [Fintype κ] [DecidableEq κ] {n' : κ → ℕ} {Ω : Type} [Field Ω]
    (y : Coord n' → Ω) (e : κ → ℕ) {s : Ω} (hs : s ∈ Geo.secM (ι := blockIdx n') y e) :
    ∃ f : MvPolynomial (Coord n') ℤ, Geo.IsMultiHomog (ι := blockIdx n') f e ∧ aeval y f = s := by sorry

alias «GroundTheory».«Heights₂».«Heights».«YPlusSmall».«exists_of_mem_secM» := P2M_GroundTheory_Heights__Heights_YPlusSmall_exists_of_mem_secM_2a2a6c5f5bc7
