-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_PGsh_DualPair__L_comp___2898f5a5a126
-- name    : P2M_ReciprocityTheory_PGsh_DualPair__L_comp___2898f5a5a126
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T13:43:31.858432+00:00
-- url     : https://prove2.me/theorems/bd78312a-e71d-4843-a193-fc705d6f6921
-- title:
--   P2 M Reciprocity Theory PGsh Dual Pair  L comp   2898f5a5a126: P2 M Reciprocity Theory PGsh Dual Pair  L comp   2898f5a5a126
-- statement:
--   The P2 M Reciprocity Theory PGsh Dual Pair  L comp   2898f5a5a126 construction uses the P2 M Reciprocity Theory PGsh Dual Pair  L comp   2898f5a5a126 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/IsFibreSq.lean#L80-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/IsFibreSq.lean#L80-L81

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

theorem P2M_ReciprocityTheory_PGsh_DualPair__L_comp___2898f5a5a126 (c : (R : Type u)) : (Dp.μL c).comp Dp.σ = Dp.σ := by sorry

alias «ReciprocityTheory».«PGsh».«DualPair».«μL_comp_σ» := P2M_ReciprocityTheory_PGsh_DualPair__L_comp___2898f5a5a126
