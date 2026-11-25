-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_MI_det_of_key
-- name    : ReciprocityTheory.ChartRestriction.G.AR.Up.MI.det_of_key
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T09:57:57.104839+00:00
-- url     : https://prove2.me/theorems/343fdb86-eacb-4581-9388-fc972ada0a1e
-- title:
--   MI: det of key
-- statement:
--   The MI construction uses the det of key property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/MeasInvStatementPfA.lean#L9-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/MeasInvStatementPfA.lean#L9-L14

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPfA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.MI
open Matrix
noncomputable section

theorem ReciprocityTheory.ChartRestriction.G.AR.Up.MI.det_of_key {m α : Type*} [Fintype m] [DecidableEq m] [LinearOrder α] {R : Type*} [CommRing R]
    (M : Matrix m m R) (κ : m → α) (hκ : Function.Injective κ)
    (h : ∀ i j, κ i < κ j → M i j = 0) : M.det = ∏ i, M i i := by sorry
