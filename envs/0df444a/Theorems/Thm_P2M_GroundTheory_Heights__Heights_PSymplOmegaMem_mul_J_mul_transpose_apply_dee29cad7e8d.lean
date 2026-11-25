-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PSymplOmegaMem_mul_J_mul_transpose_apply_dee29cad7e8d
-- name    : P2M_GroundTheory_Heights__Heights_PSymplOmegaMem_mul_J_mul_transpose_apply_dee29cad7e8d
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:14:09.18885+00:00
-- url     : https://prove2.me/theorems/f0856aed-7040-47e6-abb2-e9a60707637d
-- title:
--   P2 M Ground Theory Heights  Heights PSympl Omega Mem mul J mul transpose apply dee29cad7e8d: P2 M Ground Theory Heights  Heights PSympl Omega Mem mul J mul transpose apply dee29cad7e8d
-- statement:
--   The P2 M Ground Theory Heights  Heights PSympl Omega Mem mul J mul transpose apply dee29cad7e8d construction uses the P2 M Ground Theory Heights  Heights PSympl Omega Mem mul J mul transpose apply dee29cad7e8d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PSymplOmegaMem.lean#L11-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PSymplOmegaMem.lean#L11-L15

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsSympl
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PSymplOmegaMem
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
open Matrix
open GroundTheory.Heights₂.Heights.PSymplOmegaMem

theorem P2M_GroundTheory_Heights__Heights_PSymplOmegaMem_mul_J_mul_transpose_apply_dee29cad7e8d {R : Type*} [CommRing R] {l : Type*} [Fintype l]
    [DecidableEq l] (M : Matrix (l ⊕ l) (l ⊕ l) R) (x y : l ⊕ l) :
    (M * J l R * Mᵀ) x y = symplOmega (M x) (M y) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PSymplOmegaMem».«mul_J_mul_transpose_apply» := P2M_GroundTheory_Heights__Heights_PSymplOmegaMem_mul_J_mul_transpose_apply_dee29cad7e8d
