-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_mem_of_sum_single_eq_zero
-- name    : ReciprocityTheory.PGsh.Up.mem_of_sum_single_eq_zero
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T14:28:50.743121+00:00
-- url     : https://prove2.me/theorems/5ce7553b-8c2f-4c99-9151-84e5f0d23a1f
-- title:
--   Up: mem of sum single eq zero
-- statement:
--   The Up construction uses the mem of sum single eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/MemOfSumSingleEqZero.lean#L28-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/MemOfSumSingleEqZero.lean#L28-L35

import Definitions.Def_ReciprocityTheory_DualLattices_ProdDvdOfIso
import Definitions.Def_ReciprocityTheory_DualLattices_MemOfSumSingleEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up
variable {R : Type} [CommRing R]

theorem ReciprocityTheory.PGsh.Up.mem_of_sum_single_eq_zero {m : ℕ} (c : Fin m → R) (r : Fin m → R)
    (h : ∑ k, r k • (Pi.single k (1 : R ⧸ Ideal.span {c k}) :
      (i : Fin m) → R ⧸ Ideal.span {c i}) = 0) : ∀ i, r i ∈ Ideal.span {c i} := by sorry
