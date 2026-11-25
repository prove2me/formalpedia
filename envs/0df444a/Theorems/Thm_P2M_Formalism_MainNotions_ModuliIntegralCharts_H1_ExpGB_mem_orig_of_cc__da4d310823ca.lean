-- Prove2me | Theorems.Thm_P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGB_mem_orig_of_cc__da4d310823ca
-- name    : P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGB_mem_orig_of_cc__da4d310823ca
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T00:02:24.317794+00:00
-- url     : https://prove2.me/theorems/d7af494d-2249-4e84-a7c2-7675e7dd9d88
-- title:
--   P2 M Formalism Main Notions Moduli Integral Charts H1 Exp GB mem orig of cc  da4d310823ca: P2 M Formalism Main Notions Moduli Integral Charts H1 Exp GB mem orig of cc  da4d310823ca
-- statement:
--   The P2 M Formalism Main Notions Moduli Integral Charts H1 Exp GB mem orig of cc  da4d310823ca construction uses the P2 M Formalism Main Notions Moduli Integral Charts H1 Exp GB mem orig of cc  da4d310823ca property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/JetSubstPSTrunc.lean#L127-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/JetSubstPSTrunc.lean#L127-L129

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ScaleGenIsGen
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermBPrim
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermFunPf
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_JetSubstPSTrunc
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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGB
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermD
attribute [local instance] Over.cartesianMonoidalCategory
variable {S : Type} [CommRing S] {κ κ' : Type} [Fintype κ] [DecidableEq κ] [Fintype κ'] [DecidableEq κ']

theorem P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGB_mem_orig_of_cc__da4d310823ca (P : MvPolynomial κ S) (h : MvPolynomial.constantCoeff P = 0) : P ∈ orig S κ := by sorry

alias «Formalism».«MainNotions».«ModuliIntegralCharts».«H1».«ExpGB».«mem_orig_of_cc'» := P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGB_mem_orig_of_cc__da4d310823ca
