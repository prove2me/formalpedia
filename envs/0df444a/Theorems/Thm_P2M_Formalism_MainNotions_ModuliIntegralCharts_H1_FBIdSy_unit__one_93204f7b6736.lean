-- Prove2me | Theorems.Thm_P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_FBIdSy_unit__one_93204f7b6736
-- name    : P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_FBIdSy_unit__one_93204f7b6736
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:10:01.31888+00:00
-- url     : https://prove2.me/theorems/0e6aa80b-8fbe-4459-a63c-3ba88a08a360
-- title:
--   P2 M Formalism Main Notions Moduli Integral Charts H1 FBId Sy unit  one 93204f7b6736: P2 M Formalism Main Notions Moduli Integral Charts H1 FBId Sy unit  one 93204f7b6736
-- statement:
--   The P2 M Formalism Main Notions Moduli Integral Charts H1 FBId Sy unit  one 93204f7b6736 construction uses the P2 M Formalism Main Notions Moduli Integral Charts H1 FBId Sy unit  one 93204f7b6736 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/FBIdSy.lean#L274-L275
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/FBIdSy.lean#L274-L275

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdLB
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdJet
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CocycleRightZeroThd
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermCut
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdSy
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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdSy
open AlgebraicGeometry CategoryTheory Limits MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj NumberField
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt)
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)
variable {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) (d : ℕ) (x : ∀ m, jOG x0 d m 1 ⟶ t.G)

theorem P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_FBIdSy_unit__one_93204f7b6736 {A : Type} [CommRing A] : unitΓ (1 : Aˣ) = 1 := by sorry

alias «Formalism».«MainNotions».«ModuliIntegralCharts».«H1».«FBIdSy».«unitΓ_one» := P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_FBIdSy_unit__one_93204f7b6736
