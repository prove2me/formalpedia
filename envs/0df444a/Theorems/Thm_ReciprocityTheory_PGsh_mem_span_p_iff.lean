-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_mem_span_p_iff
-- name    : ReciprocityTheory.PGsh.mem_span_p_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:21:59.301738+00:00
-- url     : https://prove2.me/theorems/c57f53aa-d4d3-4a11-84af-c7cef0098eea
-- title:
--   PGsh: mem span p iff
-- statement:
--   The PGsh construction uses the mem span p iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/MulIterateRootEqZero.lean#L30-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/MulIterateRootEqZero.lean#L30-L42

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

theorem ReciprocityTheory.PGsh.mem_span_p_iff (x : WittVector p R) : x ∈ span {(p : WittVector p R)} ↔ x.coeff 0 = 0 := by sorry
