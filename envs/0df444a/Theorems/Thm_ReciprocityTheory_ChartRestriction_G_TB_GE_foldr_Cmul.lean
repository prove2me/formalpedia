-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_GE_foldr_Cmul
-- name    : ReciprocityTheory.ChartRestriction.G.TB.GE.foldr_Cmul
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T10:40:00.023935+00:00
-- url     : https://prove2.me/theorems/f99a3f27-9a0c-4bf8-a55d-6b31035da66c
-- title:
--   GE: foldr Cmul
-- statement:
--   The GE construction uses the foldr Cmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/GEWick.lean#L62-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/GEWick.lean#L62-L69

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_DofDApply
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GEWick
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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.GE
variable {k : Type} [CommRing k] {d : ℕ}
variable (F : Fin d → PS k 2 d) {ι : Type} [Fintype ι] (u : ι → Fin d → k)

theorem ReciprocityTheory.ChartRestriction.G.TB.GE.foldr_Cmul (L : List ι) (m : ι →₀ ℕ) (r : k) (f : PS k 1 d) :
    L.foldr (fun l h => (Dof F (u l))^[m l] h) (C r * f) =
      C r * L.foldr (fun l h => (Dof F (u l))^[m l] h) f := by sorry
