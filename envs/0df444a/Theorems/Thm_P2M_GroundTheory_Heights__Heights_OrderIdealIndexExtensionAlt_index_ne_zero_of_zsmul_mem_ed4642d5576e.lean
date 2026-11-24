-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrderIdealIndexExtensionAlt_index_ne_zero_of_zsmul_mem_ed4642d5576e
-- name    : P2M_GroundTheory_Heights__Heights_OrderIdealIndexExtensionAlt_index_ne_zero_of_zsmul_mem_ed4642d5576e
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:49:26.261258+00:00
-- url     : https://prove2.me/theorems/e7029e15-8b35-4718-80cc-5a810913d224
-- title:
--   P2 M Ground Theory Heights  Heights Order Ideal Index Extension Alt index ne zero of zsmul mem ed4642d5576e: P2 M Ground Theory Heights  Heights Order Ideal Index Extension Alt index ne zero of zsmul
-- statement:
--   The P2 M Ground Theory Heights  Heights Order Ideal Index Extension Alt index ne zero of zsmul mem ed4642d5576e construction uses the P2 M Ground Theory Heights  Heights Order Ideal Index Extension Alt index ne zero of zsmul mem ed4642d5576e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/POrderIdealIndexExtension.lean#L13-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/POrderIdealIndexExtension.lean#L13-L24

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PInvertibleIdealIndex
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_POrderIdealIndexExtension
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
open NumberField
noncomputable section
open GroundTheory.Heights₂.Heights.OrderIdealIndexExtensionAlt

theorem P2M_GroundTheory_Heights__Heights_OrderIdealIndexExtensionAlt_index_ne_zero_of_zsmul_mem_ed4642d5576e {M : Type*} [AddCommGroup M] [Module.Finite ℤ M] (H : AddSubgroup M)
    {N : ℤ} (hN : N ≠ 0) (h : ∀ x : M, N • x ∈ H) : H.index ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«OrderIdealIndexExtensionAlt».«index_ne_zero_of_zsmul_mem» := P2M_GroundTheory_Heights__Heights_OrderIdealIndexExtensionAlt_index_ne_zero_of_zsmul_mem_ed4642d5576e
