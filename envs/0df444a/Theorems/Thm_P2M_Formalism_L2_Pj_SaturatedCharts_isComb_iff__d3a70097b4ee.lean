-- Prove2me | Theorems.Thm_P2M_Formalism_L2_Pj_SaturatedCharts_isComb_iff__d3a70097b4ee
-- name    : P2M_Formalism_L2_Pj_SaturatedCharts_isComb_iff__d3a70097b4ee
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T13:31:29.137227+00:00
-- url     : https://prove2.me/theorems/86bd62e6-b164-4227-96a0-9cc5746c4852
-- title:
--   P2 M Formalism L2 Pj Saturated Charts is Comb iff  d3a70097b4ee: P2 M Formalism L2 Pj Saturated Charts is Comb iff  d3a70097b4ee
-- statement:
--   The P2 M Formalism L2 Pj Saturated Charts is Comb iff  d3a70097b4ee construction uses the P2 M Formalism L2 Pj Saturated Charts is Comb iff  d3a70097b4ee property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/SaturationChartsHolds.lean#L118-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/SaturationChartsHolds.lean#L118-L130

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

theorem P2M_Formalism_L2_Pj_SaturatedCharts_isComb_iff__d3a70097b4ee {m : ℕ} (v : Fin m → (epsOver V V ⟶ t.G)) (a : Fin m → V) (w : epsOver V V ⟶ t.G) :
    IsComb v a w ↔ w = ReciprocityTheory.ChartRestriction.G.Chart.prodPts (R := V) (G := t.G) a v := by sorry

alias «Formalism».«L2».«Pj».«SaturatedCharts».«isComb_iff'» := P2M_Formalism_L2_Pj_SaturatedCharts_isComb_iff__d3a70097b4ee
