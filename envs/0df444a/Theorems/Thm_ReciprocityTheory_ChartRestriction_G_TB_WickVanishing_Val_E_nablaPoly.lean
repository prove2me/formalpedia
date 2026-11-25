-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Val_E_nablaPoly
-- name    : ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Val.E_nablaPoly
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T10:43:15.709166+00:00
-- url     : https://prove2.me/theorems/a71ff46c-4f4d-4962-be42-2218cefaae83
-- title:
--   Val: E nabla Poly
-- statement:
--   The Val construction uses the E nabla Poly property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/HarmonicValueIntegral.lean#L133-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/HarmonicValueIntegral.lean#L133-L140

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ConnectionSecondOfCommute
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeBilinearTermEqNegDoubleSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_HarmonicValueIntegral
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_CZ_pt

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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Val
open ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab
variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
variable (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k]
variable {k}

theorem ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Val.E_nablaPoly (B : FB R d O) (h : PS k 2 d) (hax : ev (n := 1) ![0, pt k d 0] h = 0) (m : ℕ) {ι : Type}
    [Fintype ι] (u : ι → Fin d → k) (P : MvPolynomial ι k) (G : AA k d) :
    subst (bE k h) (nablaPoly k B h m u P G) = DpolyOf (B.FK k) u P (subst (bE k h) G) := by sorry
