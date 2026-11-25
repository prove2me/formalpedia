-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Geo_Tor_ValPt___ab_adaeffd89a42
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_Geo_Tor_ValPt___ab_adaeffd89a42
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:16:12.91902+00:00
-- url     : https://prove2.me/theorems/3872a802-ae82-452a-8ad9-3a0ce668dcff
-- title:
--   P2 M Reciprocity Theory Chart Restriction G Geo Tor Val Pt   ab adaeffd89a42: P2 M Reciprocity Theory Chart Restriction G Geo Tor Val Pt   ab adaeffd89a42
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G Geo Tor Val Pt   ab adaeffd89a42 construction uses the P2 M Reciprocity Theory Chart Restriction G Geo Tor Val Pt   ab adaeffd89a42 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/DvrData.lean#L79-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/DvrData.lean#L79-L84

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_FlagBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DvrData
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj
attribute [instance] UnramExt.ring UnramExt.dom UnramExt.dvr UnramExt.alg
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}

theorem P2M_ReciprocityTheory_ChartRestriction_G_Geo_Tor_ValPt___ab_adaeffd89a42 (P : ValPt Y) (W : UnramExt P.V) : (P.ξ W ⁻¹' abLocus Y.t.G).Nonempty := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«Geo».«Tor».«ValPt».«ξ_ab» := P2M_ReciprocityTheory_ChartRestriction_G_Geo_Tor_ValPt___ab_adaeffd89a42
