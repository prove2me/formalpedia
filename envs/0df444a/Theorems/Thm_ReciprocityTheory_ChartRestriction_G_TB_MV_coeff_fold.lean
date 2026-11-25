-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_MV_coeff_fold
-- name    : ReciprocityTheory.ChartRestriction.G.TB.MV.coeff_fold
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T10:40:36.873036+00:00
-- url     : https://prove2.me/theorems/652e159e-993e-460e-8d83-2a927c6229e9
-- title:
--   MV: coeff fold
-- statement:
--   The MV construction uses the coeff fold property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/MonoVal.lean#L38-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/MonoVal.lean#L38-L58

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CocycleRightZeroThd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_MonoVal
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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.MV
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {k : Type} [CommRing k] {σ : Type}

theorem ReciprocityTheory.ChartRestriction.G.TB.MV.coeff_fold {ι : Type} (cd : ι → σ) (hc : Function.Injective cd) (m : ι → ℕ) (f : MvPowerSeries σ k) :
    ∀ (L : List ι), L.Nodup → ∀ n : σ →₀ ℕ,
      coeff n (L.foldr (fun l g => (pderiv k (cd l))^[m l] g) f) =
        coeff (n + (L.map fun l => m l • Finsupp.single (cd l) 1).sum) f *
          (L.map fun l => ((n (cd l) + 1).ascFactorial (m l) : k)).prod := by sorry
