-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_SCPf_kapW_eq_kapH
-- name    : ReciprocityTheory.ChartRestriction.G.TB.SCPf.kapW_eq_kapH
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:41:56.655112+00:00
-- url     : https://prove2.me/theorems/83d0926e-2551-4bb8-9835-11fe33d70ca3
-- title:
--   SCPf: kap W eq kap H
-- statement:
--   The SCPf construction uses the kap W eq kap H property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/LemmaH.lean#L17-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/LemmaH.lean#L17-L28

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_SCWick
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LemmaH
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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.SCPf
variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
variable {k : Type} [CommRing k] [Algebra ℚ k] [Algebra R k]

theorem ReciprocityTheory.ChartRestriction.G.TB.SCPf.kapW_eq_kapH (m : ℕ) {ι π : Type} [DecidableEq π] (c : ι → π) (s : ι → Bool) (u φ : ι → Fin d → k)
    (hFU : OppositePairVanishing k c s (fun l => (0, φ l)) (fun l => (u l, 0))) :
    kapW m s (fun l => (u l, 0)) (fun l => (0, φ l)) = kapH m c s u φ := by sorry
