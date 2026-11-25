-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_dvrDataAt_all
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.Tor.dvrDataAt_all
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T14:24:47.666234+00:00
-- url     : https://prove2.me/theorems/d389421a-150d-5d69-93ed-0ae52ff40fa7
-- title:
--   Tor: dvr Data At all
-- statement:
--   The Tor construction uses the dvr Data At all property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/DvrAll.lean#L10-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/DvrAll.lean#L10-L12

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DvrAll
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open NumberField
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}

theorem ReciprocityTheory.ChartRestriction.G.Geo.Tor.dvrDataAt_all (hC : Out.CubePullSt) (hU : Out.UnramExtSt) (hB : Out.GtBaseChangeSt) (hS : Y.SplitFibres)
    (h3 : Y.N3) (P : ValPt Y) : DvrDataAt P := by sorry
