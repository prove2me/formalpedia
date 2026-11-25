-- Prove2me | Theorems.Thm_P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpOf_subst___comp1_f9ac2339a24b
-- name    : P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpOf_subst___comp1_f9ac2339a24b
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T00:01:22.118735+00:00
-- url     : https://prove2.me/theorems/263725f6-8342-429c-82d4-d6325dc87558
-- title:
--   P2 M Formalism Main Notions Moduli Integral Charts H1 Exp Of subst   comp1 f9ac2339a24b: P2 M Formalism Main Notions Moduli Integral Charts H1 Exp Of subst   comp1 f9ac2339a24b
-- statement:
--   The P2 M Formalism Main Notions Moduli Integral Charts H1 Exp Of subst   comp1 f9ac2339a24b construction uses the P2 M Formalism Main Notions Moduli Integral Charts H1 Exp Of subst   comp1 f9ac2339a24b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ExpOfPf.lean#L146-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ExpOfPf.lean#L146-L160

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpTie
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ExpLaw
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_PderivSecondEvFirstPointEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ActLin
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpOfPf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_CZ_pt

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

theorem P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpOf_subst___comp1_f9ac2339a24b (uvec : Lt1 Dw → Fin d → S) (ε : Pt S 1 d) (b : Fin 2) (i : Fin d) :
    subst (fun p : Fin 2 × Fin d => linPt uvec p.1 p.2) (comp1 ε (pt S (n := 2) d b) i) =
      subst (fun q : Fin 1 × Fin d => linPt uvec b q.2) (ε i) := by sorry

alias «Formalism».«MainNotions».«ModuliIntegralCharts».«H1».«ExpOf».«subst_Λ_comp1» := P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpOf_subst___comp1_f9ac2339a24b
