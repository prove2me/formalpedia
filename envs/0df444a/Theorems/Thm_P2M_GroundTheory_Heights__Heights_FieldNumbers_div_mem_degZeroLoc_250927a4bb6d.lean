-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_div_mem_degZeroLoc_250927a4bb6d
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_div_mem_degZeroLoc_250927a4bb6d
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T06:05:42.523848+00:00
-- url     : https://prove2.me/theorems/464e268f-7448-5369-963c-6caa684fd20a
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers div mem deg Zero Loc 250927a4bb6d: P2 M Ground Theory Heights  Heights Field Numbers div mem deg Zero Loc 250927a4bb6d
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers div mem deg Zero Loc 250927a4bb6d construction uses the P2 M Ground Theory Heights  Heights Field Numbers div mem deg Zero Loc 250927a4bb6d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/StatementsDegZeroLoc.lean#L23-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/StatementsDegZeroLoc.lean#L23-L28

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDivPushForwardLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPFDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDegZeroLoc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
variable {K : Type*} [DecidableEq K] {ι : K → Type*} {F : Type*} [Field F]

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_div_mem_degZeroLoc_250927a4bb6d (P : Ideal (MRing ι F)) [P.IsPrime] (𝒲 : Set (Ideal (MRing ι F)))
    {b : K → ℕ} {f g : MRing ι F} (hf : IsMultiHomog f b) (hg : IsMultiHomog g b) (hgP : g ∉ P)
    (hg𝒲 : ∀ W ∈ 𝒲, g ∉ W) :
    algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P)) (Ideal.Quotient.mk P f) /
      algebraMap (MRing ι F ⧸ P) _ (Ideal.Quotient.mk P g) ∈ degZeroLoc P 𝒲 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«div_mem_degZeroLoc» := P2M_GroundTheory_Heights__Heights_FieldNumbers_div_mem_degZeroLoc_250927a4bb6d
