-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_eq_xz
-- name    : ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.eq_xz
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T10:44:38.585802+00:00
-- url     : https://prove2.me/theorems/4d1a3f3b-5f1d-5038-b206-dc438a8dfefe
-- title:
--   Wick Vanishing: eq xz
-- statement:
--   The Wick Vanishing construction uses the eq xz property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/HStable.lean#L15-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/HStable.lean#L15-L50

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeBilinearTermEqNegDoubleSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_HStable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Finsupp
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
variable {d : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.eq_xz {n : Fin 2 × Fin d →₀ ℕ} {l m : Fin d} (h0 : n (0, l) ≠ 0) (h1 : n (1, m) ≠ 0) (hd : n.degree ≤ 2) :
    n = single ((0 : Fin 2), l) 1 + single ((1 : Fin 2), m) 1 := by sorry
