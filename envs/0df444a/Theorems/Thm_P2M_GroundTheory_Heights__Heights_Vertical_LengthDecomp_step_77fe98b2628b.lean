-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_LengthDecomp_step_77fe98b2628b
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_LengthDecomp_step_77fe98b2628b
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:28:16.538792+00:00
-- url     : https://prove2.me/theorems/8fc43b1a-405d-491b-b38f-dac42860970a
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Length Decomp step 77fe98b2628b: P2 M Ground Theory Heights  Heights Vertical Length Decomp step 77fe98b2628b
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Length Decomp step 77fe98b2628b construction uses the P2 M Ground Theory Heights  Heights Vertical Length Decomp step 77fe98b2628b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PLengthDecomp.lean#L59-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PLengthDecomp.lean#L59-L84

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PLengthDecomp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open Module IsLocalRing LinearMap Submodule
noncomputable section
open GroundTheory.Heights₂.Heights.Vertical.LengthDecomp
open Classical
variable {B : Type*} [CommRing B]
variable {R : Type*} [CommRing R] [Algebra R B]
variable {N : Type*} [AddCommGroup N] [Module B N] [Module R N] [IsScalarTower R B N]

theorem P2M_GroundTheory_Heights__Heights_Vertical_LengthDecomp_step_77fe98b2628b {p q : Submodule B N} (h : p ⋖ q) :
    ∃ m : MaximalSpectrum B, length R q = length R p + length R (B ⧸ m.asIdeal) ∧
      ∀ n : MaximalSpectrum B,
        length (Localization.AtPrime n.asIdeal) (LocalizedModule n.asIdeal.primeCompl q) =
          length (Localization.AtPrime n.asIdeal) (LocalizedModule n.asIdeal.primeCompl p) +
            if n = m then 1 else 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«LengthDecomp».«step» := P2M_GroundTheory_Heights__Heights_Vertical_LengthDecomp_step_77fe98b2628b
