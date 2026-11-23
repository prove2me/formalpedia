-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_p_mul_eq_zero
-- name    : ReciprocityTheory.PGsh.p_mul_eq_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:21:59.347547+00:00
-- url     : https://prove2.me/theorems/19d9a921-c99a-4a50-ac63-65dff12668cf
-- title:
--   PGsh: p mul eq zero
-- statement:
--   The PGsh construction uses the p mul eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/MulIterateRootEqZero.lean#L44-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/MulIterateRootEqZero.lean#L44-L51

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

theorem ReciprocityTheory.PGsh.p_mul_eq_zero (x : WittVector p R) (h : x * p = 0) : x = 0 := by sorry
