-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PGaussFourierSelf_ofReal_gauss_3cb7d6e7b62c
-- name    : P2M_GroundTheory_Heights__Heights_PGaussFourierSelf_ofReal_gauss_3cb7d6e7b62c
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T04:13:46.301841+00:00
-- url     : https://prove2.me/theorems/db8a327b-991e-4944-84a4-295dba5aa04b
-- title:
--   P2 M Ground Theory Heights  Heights PGauss Fourier Self of Real gauss 3cb7d6e7b62c: P2 M Ground Theory Heights  Heights PGauss Fourier Self of Real gauss 3cb7d6e7b62c
-- statement:
--   The P2 M Ground Theory Heights  Heights PGauss Fourier Self of Real gauss 3cb7d6e7b62c construction uses the P2 M Ground Theory Heights  Heights PGauss Fourier Self of Real gauss 3cb7d6e7b62c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PGaussFourierSelf.lean#L12-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PGaussFourierSelf.lean#L12-L16

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGauss
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PGaussFourierSelf
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
open Real MeasureTheory
open scoped FourierTransform
open GroundTheory.Heights₂.Heights.PGaussFourierSelf

theorem P2M_GroundTheory_Heights__Heights_PGaussFourierSelf_ofReal_gauss_3cb7d6e7b62c {V : Type*} [NormedAddCommGroup V] (x : V) :
    ((Real.exp (-π * ‖x‖ ^ 2) : ℝ) : ℂ) = Complex.exp (-(π : ℂ) * (‖x‖ : ℂ) ^ 2) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PGaussFourierSelf».«ofReal_gauss» := P2M_GroundTheory_Heights__Heights_PGaussFourierSelf_ofReal_gauss_3cb7d6e7b62c
