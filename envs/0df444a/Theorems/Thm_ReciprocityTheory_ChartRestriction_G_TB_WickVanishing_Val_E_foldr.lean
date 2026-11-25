-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Val_E_foldr
-- name    : ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Val.E_foldr
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:42:53.745846+00:00
-- url     : https://prove2.me/theorems/75e0e234-1710-507e-a769-4626e9459b41
-- title:
--   Val: E foldr
-- statement:
--   The Val construction uses the E foldr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/HarmonicValueIntegral.lean#L123-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/HarmonicValueIntegral.lean#L123-L131

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

theorem ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Val.E_foldr (B : FB R d O) (h : PS k 2 d) (hax : ev (n := 1) ![0, pt k d 0] h = 0) (m : ℕ) {ι : Type}
    (u : ι → Fin d → k) (n : ι →₀ ℕ) (L : List ι) (G : AA k d) :
    subst (bE k h) (L.foldr (fun l g => (nabla k B h m (u l) 0)^[n l] g) G) =
      L.foldr (fun l g => (Dof (B.FK k) (u l))^[n l] g) (subst (bE k h) G) := by sorry
