-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_coeff_subst_xz
-- name    : ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.coeff_subst_xz
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:26:53.885482+00:00
-- url     : https://prove2.me/theorems/9e7c5abc-d837-455e-9f00-cd02e8b0d36e
-- title:
--   Wick Vanishing: coeff subst xz
-- statement:
--   The Wick Vanishing construction uses the coeff subst xz property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/HStable.lean#L75-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/HStable.lean#L75-L127

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
variable {k : Type} [CommRing k] {d : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.coeff_subst_xz {τ : Type*} (h : PS k 2 d) (h0 : ev (n := 1) ![0, pt k d 0] h = 0)
    (h1 : ev (n := 1) ![pt k d 0, 0] h = 0) (a : Fin 2 × Fin d → MvPowerSeries τ k)
    (ha : ∀ s, constantCoeff (a s) = 0) (n : τ →₀ ℕ) (hn : n.degree = 2) :
    coeff n (subst a h) = ∑ l, ∑ m, coeff (single ((0 : Fin 2), l) 1 + single ((1 : Fin 2), m) 1) h *
      coeff n (a (0, l) * a (1, m)) := by sorry
