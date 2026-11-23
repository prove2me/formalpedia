-- Prove2me | Theorems.Thm_P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpOf_hasSubst___01ac09189af3
-- name    : P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpOf_hasSubst___01ac09189af3
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:03:12.929268+00:00
-- url     : https://prove2.me/theorems/f2b6bb41-8a15-49bc-b39b-f09b3680d576
-- title:
--   P2 M Formalism Main Notions Moduli Integral Charts H1 Exp Of has Subst   01ac09189af3: P2 M Formalism Main Notions Moduli Integral Charts H1 Exp Of has Subst   01ac09189af3
-- statement:
--   The P2 M Formalism Main Notions Moduli Integral Charts H1 Exp Of has Subst   01ac09189af3 construction uses the P2 M Formalism Main Notions Moduli Integral Charts H1 Exp Of has Subst   01ac09189af3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ExpOfPf.lean#L142-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ExpOfPf.lean#L142-L144

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpTie
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ExpLaw
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_PderivSecondEvFirstPointEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ActLin
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpOfPf
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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1.ExpOf
variable {S : Type} [CommRing S] [Algebra ℚ S]
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {d : ℕ}

theorem P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpOf_hasSubst___01ac09189af3 (uvec : Lt1 Dw → Fin d → S) :
    HasSubst (fun p : Fin 2 × Fin d => linPt uvec p.1 p.2) := by sorry

alias «Formalism».«MainNotions».«ModuliIntegralCharts».«H1».«ExpOf».«hasSubst_Λ» := P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpOf_hasSubst___01ac09189af3
