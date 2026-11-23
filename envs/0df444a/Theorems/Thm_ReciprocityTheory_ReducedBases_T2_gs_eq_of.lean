-- Prove2me | Theorems.Thm_ReciprocityTheory_ReducedBases_T2_gs_eq_of
-- name    : ReciprocityTheory.ReducedBases.T2.gs_eq_of
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:32:24.220807+00:00
-- url     : https://prove2.me/theorems/4979f523-761c-4e97-bf57-994d254c73e4
-- title:
--   T2: gs eq of
-- statement:
--   The T2 construction uses the gs eq of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReducedBases/GsInnerBOfLt.lean#L48-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReducedBases/GsInnerBOfLt.lean#L48-L63

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

theorem ReciprocityTheory.ReducedBases.T2.gs_eq_of (b : Fin d → E) (k : Fin d) (v : E) (h1 : b k - v ∈ span ℝ (b '' Set.Iio k))
    (h2 : ∀ j < k, ⟪v, b j⟫_ℝ = 0) : gs b k = v := by sorry
