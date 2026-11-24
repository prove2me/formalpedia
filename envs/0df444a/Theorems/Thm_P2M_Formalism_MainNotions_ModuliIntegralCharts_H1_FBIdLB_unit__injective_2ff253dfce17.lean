-- Prove2me | Theorems.Thm_P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_FBIdLB_unit__injective_2ff253dfce17
-- name    : P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_FBIdLB_unit__injective_2ff253dfce17
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:06:43.701844+00:00
-- url     : https://prove2.me/theorems/5db51686-d071-4ac8-9da7-092d5b93b865
-- title:
--   P2 M Formalism Main Notions Moduli Integral Charts H1 FBId LB unit  injective 2ff253dfce17: P2 M Formalism Main Notions Moduli Integral Charts H1 FBId LB unit  injective 2ff253dfce17
-- statement:
--   The P2 M Formalism Main Notions Moduli Integral Charts H1 FBId LB unit  injective 2ff253dfce17 construction uses the P2 M Formalism Main Notions Moduli Integral Charts H1 FBId LB unit  injective 2ff253dfce17 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/FBIdLB.lean#L105-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/FBIdLB.lean#L105-L111

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsChartIff
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermDJet
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBCorr
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBTransport
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdLB
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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdLB
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj NumberField
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)
variable {Y Z : Scheme.{0}} {K K' : Type} [Fintype K] [Fintype K']
variable {S : Type} [CommRing S] (x0 : Sp S ⟶ X0)

theorem P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_FBIdLB_unit__injective_2ff253dfce17 {A : Type} [CommRing A] : Function.Injective (unitΓ (A := A)) := by sorry

alias «Formalism».«MainNotions».«ModuliIntegralCharts».«H1».«FBIdLB».«unitΓ_injective» := P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_FBIdLB_unit__injective_2ff253dfce17
