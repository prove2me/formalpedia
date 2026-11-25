-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_psd_det_re_le_one_of_diag
-- name    : ReciprocityTheory.ChartRestriction.G.T0.psd_det_re_le_one_of_diag
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T10:38:56.234871+00:00
-- url     : https://prove2.me/theorems/1a79293e-d372-4ec6-826a-5992e1dd1a5f
-- title:
--   T0: psd det re le one of diag
-- statement:
--   The T0 construction uses the psd det re le one of diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/Hadamard.lean#L8-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/Hadamard.lean#L8-L28

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

theorem ReciprocityTheory.ChartRestriction.G.T0.psd_det_re_le_one_of_diag (N : ℕ) (H : Matrix (Fin N) (Fin N) ℂ) (hH : H.PosSemidef)
    (hd : ∀ c, H c c = 1) : H.det.re ≤ 1 := by sorry
