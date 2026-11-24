-- Prove2me | Theorems.Thm_P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGG_law__a_b638aaa98346
-- name    : P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGG_law__a_b638aaa98346
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:22:01.59417+00:00
-- url     : https://prove2.me/theorems/c46bb0b0-9beb-478a-8cf0-e40ca49ba726
-- title:
--   P2 M Formalism Main Notions Moduli Integral Charts H1 Exp GG law  a b638aaa98346: P2 M Formalism Main Notions Moduli Integral Charts H1 Exp GG law  a b638aaa98346
-- statement:
--   The P2 M Formalism Main Notions Moduli Integral Charts H1 Exp GG law  a b638aaa98346 construction uses the P2 M Formalism Main Notions Moduli Integral Charts H1 Exp GG law  a b638aaa98346 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/HasSubstActPS.lean#L53-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/HasSubstActPS.lean#L53-L90

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

theorem P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGG_law__a_b638aaa98346 {d : ℕ} {F : Fin d → MvPowerSeries (Fin 2 × Fin d) S} {uvec : Lt1 Dw → Fin d → S}
    {φ : Fin d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S} (hφ : IsExpOf F uvec φ) (u v : 𝓞 E) (j : Fin d) :
    subst (fun p : Fin 2 × Fin d => φa c φ (![u, v] p.1) p.2) (F j) = φa c φ (u + v) j := by sorry

alias «Formalism».«MainNotions».«ModuliIntegralCharts».«H1».«ExpGG».«law_φa» := P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGG_law__a_b638aaa98346
