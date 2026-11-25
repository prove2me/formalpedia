-- Prove2me | Theorems.Thm_P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGG__a_mul_3f365165b132
-- name    : P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGG__a_mul_3f365165b132
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T00:02:13.961595+00:00
-- url     : https://prove2.me/theorems/a7aef67b-9466-4bcc-a820-074352a0e434
-- title:
--   P2 M Formalism Main Notions Moduli Integral Charts H1 Exp GG  a mul 3f365165b132: P2 M Formalism Main Notions Moduli Integral Charts H1 Exp GG  a mul 3f365165b132
-- statement:
--   The P2 M Formalism Main Notions Moduli Integral Charts H1 Exp GG  a mul 3f365165b132 construction uses the P2 M Formalism Main Notions Moduli Integral Charts H1 Exp GG  a mul 3f365165b132 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/HasSubstActPS.lean#L30-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/HasSubstActPS.lean#L30-L36

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_JetSubstPSEqJetMap
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_UnitIdSt
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_HasSubstActPS
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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGG
open MvPowerSeries NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGU
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {S : Type} [CommRing S] (c : Coeff l) [Algebra c.F S]

theorem P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGG__a_mul_3f365165b132 {d : ℕ} (φ : Fin d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S) (u v : 𝓞 E) (j : Fin d) :
    subst (actPS (Dw := Dw) c v) (φa c φ u j) = φa c φ (u * v) j := by sorry

alias «Formalism».«MainNotions».«ModuliIntegralCharts».«H1».«ExpGG».«φa_mul» := P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGG__a_mul_3f365165b132
