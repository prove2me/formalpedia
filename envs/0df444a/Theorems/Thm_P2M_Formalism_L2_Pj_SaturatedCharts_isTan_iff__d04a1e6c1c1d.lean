-- Prove2me | Theorems.Thm_P2M_Formalism_L2_Pj_SaturatedCharts_isTan_iff__d04a1e6c1c1d
-- name    : P2M_Formalism_L2_Pj_SaturatedCharts_isTan_iff__d04a1e6c1c1d
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T13:28:15.378172+00:00
-- url     : https://prove2.me/theorems/248bb497-f640-592d-8e13-d3aee78c4398
-- title:
--   P2 M Formalism L2 Pj Saturated Charts is Tan iff  d04a1e6c1c1d: P2 M Formalism L2 Pj Saturated Charts is Tan iff  d04a1e6c1c1d
-- statement:
--   The P2 M Formalism L2 Pj Saturated Charts is Tan iff  d04a1e6c1c1d construction uses the P2 M Formalism L2 Pj Saturated Charts is Tan iff  d04a1e6c1c1d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/SaturationChartsHolds.lean#L114-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/SaturationChartsHolds.lean#L114-L116

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ChartDirectionsIntegral
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExistsBasisOfSaturated
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_LieEig
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_ChartLaw
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_SaturationChartsHolds
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
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.SaturatedCharts
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {V : Type} [CommRing V]
variable (t : SAB H (Sp V))

theorem P2M_Formalism_L2_Pj_SaturatedCharts_isTan_iff__d04a1e6c1c1d (w : epsOver V V ⟶ t.G) :
    IsTan w ↔ ReciprocityTheory.ChartRestriction.G.Chart.IsTan (R := V) (G := t.G) w := by sorry

alias «Formalism».«L2».«Pj».«SaturatedCharts».«isTan_iff'» := P2M_Formalism_L2_Pj_SaturatedCharts_isTan_iff__d04a1e6c1c1d
