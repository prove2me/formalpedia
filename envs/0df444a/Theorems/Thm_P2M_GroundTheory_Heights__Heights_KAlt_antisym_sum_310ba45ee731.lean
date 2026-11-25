-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_KAlt_antisym_sum_310ba45ee731
-- name    : P2M_GroundTheory_Heights__Heights_KAlt_antisym_sum_310ba45ee731
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:24:46.942034+00:00
-- url     : https://prove2.me/theorems/ad5fefa2-1568-4645-a5ff-3b725d4d2fa6
-- title:
--   P2 M Ground Theory Heights  Heights KAlt antisym sum 310ba45ee731: P2 M Ground Theory Heights  Heights KAlt antisym sum 310ba45ee731
-- statement:
--   The P2 M Ground Theory Heights  Heights KAlt antisym sum 310ba45ee731 construction uses the P2 M Ground Theory Heights  Heights KAlt antisym sum 310ba45ee731 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/AltPush.lean#L53-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/AltPush.lean#L53-L56

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KernelsRest
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_AltPush
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
open MvPolynomial Finset
noncomputable section
open GroundTheory.Heights₂.Heights.KAlt
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem P2M_GroundTheory_Heights__Heights_KAlt_antisym_sum_310ba45ee731 {κ : Type*} (s : Finset κ) (f : κ → MvPolynomial ι ℚ) :
    antisym (∑ x ∈ s, f x) = ∑ x ∈ s, antisym (f x) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«KAlt».«antisym_sum» := P2M_GroundTheory_Heights__Heights_KAlt_antisym_sum_310ba45ee731
