-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_p_mem_nonZeroDivisors
-- name    : ReciprocityTheory.PGsh.p_mem_nonZeroDivisors
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T11:09:32.443927+00:00
-- url     : https://prove2.me/theorems/594f0cbd-3b96-44ed-b68e-71e1cf5a2a03
-- title:
--   PGsh: p mem non Zero Divisors
-- statement:
--   The PGsh construction uses the p mem non Zero Divisors property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/MulIterateRootEqZero.lean#L53-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/MulIterateRootEqZero.lean#L53-L54

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_CyclicRecursionStatement
import Definitions.Def_ReciprocityTheory_DualLattices_MulIterateRootEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open WittVector Ideal TensorProduct
open ReciprocityTheory ReciprocityTheory.PGsh
variable {p : ℕ} [hp : Fact p.Prime] {R : Type*} [CommRing R] [CharP R p] [PerfectRing R p]

theorem ReciprocityTheory.PGsh.p_mem_nonZeroDivisors : (p : WittVector p R) ∈ nonZeroDivisors (WittVector p R) := by sorry
