-- Prove2me | Theorems.Thm_P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_CIndFrFix2b_cc_pt__5e1994025291
-- name    : P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_CIndFrFix2b_cc_pt__5e1994025291
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T14:31:31.081801+00:00
-- url     : https://prove2.me/theorems/60f6f978-ed89-54e8-aba1-36aa496e3b33
-- title:
--   P2 M Formalism Main Notions Moduli Integral Charts H1 CInd Fr Fix2b cc pt  5e1994025291: P2 M Formalism Main Notions Moduli Integral Charts H1 CInd Fr Fix2b cc pt  5e1994025291
-- statement:
--   The P2 M Formalism Main Notions Moduli Integral Charts H1 CInd Fr Fix2b cc pt  5e1994025291 construction uses the P2 M Formalism Main Notions Moduli Integral Charts H1 CInd Fr Fix2b cc pt  5e1994025291 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ConstantCoeffAddSecondThird.lean#L28-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ConstantCoeffAddSecondThird.lean#L28-L29

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndFrFix
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThetaSwapFirstTwo
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcAdd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ActLin
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ExpLaw
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_HomUniq
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_PderivSecondEvFirstPointEqZero
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ConstantCoeffAddSecondThird
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_CZ_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_ev_X
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_ev_ev
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_ev_X
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_ev_ev
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_exp_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_hasSubst_pts
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_subst_exp

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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix2b
open MvPolynomial Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix ReciprocityTheory.ChartRestriction.G.TB
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw FB)
variable {S : Type} [CommRing S] [Algebra ℚ S] {d : ℕ}
open ReciprocityTheory.ChartRestriction.G.TB.WickVanishing (ev_ev ev_X hasSubst_pts exp_add subst_exp)

theorem P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_CIndFrFix2b_cc_pt__5e1994025291 {n : ℕ} (j : Fin n) (i : Fin d) : MvPowerSeries.constantCoeff (pt S d j i) = 0 := by sorry

alias «Formalism».«MainNotions».«ModuliIntegralCharts».«H1».«CIndFrFix2b».«cc_pt'» := P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_CIndFrFix2b_cc_pt__5e1994025291
