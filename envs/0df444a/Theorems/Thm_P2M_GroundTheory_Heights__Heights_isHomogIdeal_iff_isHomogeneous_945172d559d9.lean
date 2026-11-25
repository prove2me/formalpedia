-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_isHomogIdeal_iff_isHomogeneous_945172d559d9
-- name    : P2M_GroundTheory_Heights__Heights_isHomogIdeal_iff_isHomogeneous_945172d559d9
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:47:24.559327+00:00
-- url     : https://prove2.me/theorems/ba03fd8f-c059-4e34-b3bc-023cd998e4de
-- title:
--   P2 M Ground Theory Heights  Heights is Homog Ideal iff is Homogeneous 945172d559d9: P2 M Ground Theory Heights  Heights is Homog Ideal iff is Homogeneous 945172d559d9
-- statement:
--   The P2 M Ground Theory Heights  Heights is Homog Ideal iff is Homogeneous 945172d559d9 construction uses the P2 M Ground Theory Heights  Heights is Homog Ideal iff is Homogeneous 945172d559d9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PDivCyclePrime.lean#L13-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PDivCyclePrime.lean#L13-L22

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsMahler
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PDivCyclePrime
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
open MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_isHomogIdeal_iff_isHomogeneous_945172d559d9 (I : Ideal (MvPolynomial (Fin n) ℂ)) :
    IsHomogIdeal I ↔ I.IsHomogeneous (homogeneousSubmodule (Fin n) ℂ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«isHomogIdeal_iff_isHomogeneous» := P2M_GroundTheory_Heights__Heights_isHomogIdeal_iff_isHomogeneous_945172d559d9
