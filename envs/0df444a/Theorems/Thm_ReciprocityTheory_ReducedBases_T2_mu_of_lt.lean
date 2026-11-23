-- Prove2me | Theorems.Thm_ReciprocityTheory_ReducedBases_T2_mu_of_lt
-- name    : ReciprocityTheory.ReducedBases.T2.mu_of_lt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:33:36.049771+00:00
-- url     : https://prove2.me/theorems/4f4e5240-e834-4559-b586-0a1ace5c3b7f
-- title:
--   T2: mu of lt
-- statement:
--   The T2 construction uses the mu of lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReducedBases/GsInnerBOfLt.lean#L78-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReducedBases/GsInnerBOfLt.lean#L78-L80

import Mathlib
import Definitions.Def_ReciprocityTheory_ReducedBases_GsInnerBOfLt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ReducedBases ReciprocityTheory.ReducedBases.T2
open Finset InnerProductSpace Submodule
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {d : ℕ}

theorem ReciprocityTheory.ReducedBases.T2.mu_of_lt (b : Fin d → E) {i j : Fin d} (h : i < j) : mu b i j = 0 := by sorry
