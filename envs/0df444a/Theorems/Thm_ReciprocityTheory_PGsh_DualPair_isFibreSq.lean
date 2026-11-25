-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_DualPair_isFibreSq
-- name    : ReciprocityTheory.PGsh.DualPair.isFibreSq
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:05:49.872871+00:00
-- url     : https://prove2.me/theorems/e881e999-09f5-42b7-a1f5-bb0d4185b78e
-- title:
--   Dual Pair: is Fibre Sq
-- statement:
--   The Dual Pair construction uses the is Fibre Sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/IsFibreSq.lean#L194-L199
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/IsFibreSq.lean#L194-L199

import Definitions.Def_ReciprocityTheory_DualLattices_ModuliPointsState
import Definitions.Def_ReciprocityTheory_DualLattices_IsFibreSq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.PGsh
universe u
variable {R₀ : Type u} [CommRing R₀]
open ReciprocityTheory.PGsh.DualPair
variable {R : LAlg R₀} (Dp : DualPair R)

theorem ReciprocityTheory.PGsh.DualPair.isFibreSq : IsFibreSq Dp.p₁L Dp.p₂L Dp.π Dp.π := by sorry
