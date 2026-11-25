-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_re_mul_of_pos_8ae9e150c1fd
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_re_mul_of_pos_8ae9e150c1fd
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T10:43:21.164911+00:00
-- url     : https://prove2.me/theorems/a3c2fec6-1f40-4162-9370-8fb923da0cec
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kernels re mul of pos 8ae9e150c1fd: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kernels re mul of pos 8ae9e150
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kernels re mul of pos 8ae9e150c1fd construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kernels re mul of pos 8ae9e150c1fd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ReMulOfPos.lean#L22-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ReMulOfPos.lean#L22-L25

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ImportsBis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ReMulOfPos
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
open NumberField NumberField.ComplexEmbedding Matrix GroundTheory.Heights₂.Heights
open scoped nonZeroDivisors ComplexOrder
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_re_mul_of_pos_8ae9e150c1fd {x : ℂ} (y : ℂ) (hx : 0 < x) : (x * y).re = x.re * y.re := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Kernels».«re_mul_of_pos» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_re_mul_of_pos_8ae9e150c1fd
