-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_DualPair_natCast_D
-- name    : ReciprocityTheory.PGsh.DualPair.natCast_D
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:16:24.469785+00:00
-- url     : https://prove2.me/theorems/0da694bf-1e12-4f10-84b4-94ecae99ff73
-- title:
--   Dual Pair: nat Cast D
-- statement:
--   The Dual Pair construction uses the nat Cast D property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/NilSurjOfSqZero.lean#L214-L215
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/NilSurjOfSqZero.lean#L214-L215

import Definitions.Def_ReciprocityTheory_DualLattices_ModuliPointsState
import Definitions.Def_ReciprocityTheory_DualLattices_NilSurjOfSqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct
open ReciprocityTheory ReciprocityTheory.PGsh
universe u
variable {R₀ : Type u} [CommRing R₀]
open ReciprocityTheory.PGsh.DualPair
variable {R : LAlg R₀} (Dp : DualPair R)

theorem ReciprocityTheory.PGsh.DualPair.natCast_D {N : ℕ} (hN : (N : (R : Type u)) = 0) : (N : (Dp.D : Type u)) = 0 := by sorry
