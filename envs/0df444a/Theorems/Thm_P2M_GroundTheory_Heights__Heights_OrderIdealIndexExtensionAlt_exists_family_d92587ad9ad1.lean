-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrderIdealIndexExtensionAlt_exists_family_d92587ad9ad1
-- name    : P2M_GroundTheory_Heights__Heights_OrderIdealIndexExtensionAlt_exists_family_d92587ad9ad1
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:13:24.983559+00:00
-- url     : https://prove2.me/theorems/3cd1e79d-f28e-4b05-8274-c77e302e8f8f
-- title:
--   P2 M Ground Theory Heights  Heights Order Ideal Index Extension Alt exists family d92587ad9ad1: P2 M Ground Theory Heights  Heights Order Ideal Index Extension Alt exists family d92587ad9ad1
-- statement:
--   The P2 M Ground Theory Heights  Heights Order Ideal Index Extension Alt exists family d92587ad9ad1 construction uses the P2 M Ground Theory Heights  Heights Order Ideal Index Extension Alt exists family d92587ad9ad1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/POrderIdealIndexExtension.lean#L53-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/POrderIdealIndexExtension.lean#L53-L107

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
variable {L : Type} [Field L]
variable [NumberField L] {B : Subring L} [Module.Finite ℤ B]

theorem P2M_GroundTheory_Heights__Heights_OrderIdealIndexExtensionAlt_exists_family_d92587ad9ad1 : ∃ S : Set (𝓞 L), S.Finite ∧ LinearIndepOn B (fun x : 𝓞 L => (x : L)) S ∧
    ∃ N : ℤ, N ≠ 0 ∧ ∀ x : 𝓞 L,
      (N : L) * (x : L) ∈ Submodule.span B ((fun x : 𝓞 L => (x : L)) '' S) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«OrderIdealIndexExtensionAlt».«exists_family» := P2M_GroundTheory_Heights__Heights_OrderIdealIndexExtensionAlt_exists_family_d92587ad9ad1
