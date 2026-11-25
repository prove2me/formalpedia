-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_psd_det_re_le_prod_diag
-- name    : ReciprocityTheory.ChartRestriction.G.T0.psd_det_re_le_prod_diag
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T10:38:18.408122+00:00
-- url     : https://prove2.me/theorems/4733f3dd-066e-5546-9ad9-92f9b7313275
-- title:
--   T0: psd det re le prod diag
-- statement:
--   The T0 construction uses the psd det re le prod diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/Hadamard.lean#L30-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/Hadamard.lean#L30-L86

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

theorem ReciprocityTheory.ChartRestriction.G.T0.psd_det_re_le_prod_diag (N : ℕ) (G : Matrix (Fin N) (Fin N) ℂ) (hG : G.PosSemidef) :
    G.det.re ≤ ∏ c, (G c c).re := by sorry
