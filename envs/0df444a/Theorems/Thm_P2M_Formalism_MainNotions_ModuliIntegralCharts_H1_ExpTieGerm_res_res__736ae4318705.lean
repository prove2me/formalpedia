-- Prove2me | Theorems.Thm_P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpTieGerm_res_res__736ae4318705
-- name    : P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpTieGerm_res_res__736ae4318705
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:01:35.422552+00:00
-- url     : https://prove2.me/theorems/94f81322-4c57-46ee-b928-be469f6db631
-- title:
--   P2 M Formalism Main Notions Moduli Integral Charts H1 Exp Tie Germ res res  736ae4318705: P2 M Formalism Main Notions Moduli Integral Charts H1 Exp Tie Germ res res  736ae4318705
-- statement:
--   The P2 M Formalism Main Notions Moduli Integral Charts H1 Exp Tie Germ res res  736ae4318705 construction uses the P2 M Formalism Main Notions Moduli Integral Charts H1 Exp Tie Germ res res  736ae4318705 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ExpTieGerm.lean#L16-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ExpTieGerm.lean#L16-L18

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpTieAlg
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermFunPf
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermDVal
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpTieGerm
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_DVR_res_res__b0a8af1c3378

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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpTieGerm
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

theorem P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpTieGerm_res_res__736ae4318705 {X : Scheme.{0}} {U V W : X.Opens} (h1 : V ≤ U) (h2 : W ≤ V) (x : Γ(X, U)ˣ) :
    res h2 (res h1 x) = res (h2.trans h1) x := by sorry

alias «Formalism».«MainNotions».«ModuliIntegralCharts».«H1».«ExpTieGerm».«res_res'» := P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpTieGerm_res_res__736ae4318705
