-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_hadamard_det_le
-- name    : ReciprocityTheory.ChartRestriction.G.T0.hadamard_det_le
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T17:03:00.77767+00:00
-- url     : https://prove2.me/theorems/6cfeb5a4-1145-43ff-a17d-f8f69f37042c
-- title:
--   T0: hadamard det le
-- statement:
--   The T0 construction uses the hadamard det le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/Hadamard.lean#L88-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/Hadamard.lean#L88-L112

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_Hadamard
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open scoped BigOperators ComplexOrder
open Finset Matrix

theorem ReciprocityTheory.ChartRestriction.G.T0.hadamard_det_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    ‖A.det‖ ≤ ∏ i, Real.sqrt (∑ j, ‖A i j‖ ^ 2) := by sorry
