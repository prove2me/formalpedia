-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_KAlt_antisym_permTerm_76dab284b23e
-- name    : P2M_GroundTheory_Heights__Heights_KAlt_antisym_permTerm_76dab284b23e
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:24:34.309642+00:00
-- url     : https://prove2.me/theorems/194f62ee-0134-4be6-a9dd-a79121c11d84
-- title:
--   P2 M Ground Theory Heights  Heights KAlt antisym perm Term 76dab284b23e: P2 M Ground Theory Heights  Heights KAlt antisym perm Term 76dab284b23e
-- statement:
--   The P2 M Ground Theory Heights  Heights KAlt antisym perm Term 76dab284b23e construction uses the P2 M Ground Theory Heights  Heights KAlt antisym perm Term 76dab284b23e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/AltPush.lean#L44-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/AltPush.lean#L44-L51

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

theorem P2M_GroundTheory_Heights__Heights_KAlt_antisym_permTerm_76dab284b23e (e : ι → ℕ) (π : Equiv.Perm ι) :
    antisym (permTerm e π) = sgnP π * alternant e := by sorry

alias «GroundTheory».«Heights₂».«Heights».«KAlt».«antisym_permTerm» := P2M_GroundTheory_Heights__Heights_KAlt_antisym_permTerm_76dab284b23e
