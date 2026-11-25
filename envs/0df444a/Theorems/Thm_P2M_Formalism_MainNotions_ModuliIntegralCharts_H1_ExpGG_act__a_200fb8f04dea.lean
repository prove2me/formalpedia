-- Prove2me | Theorems.Thm_P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGG_act__a_200fb8f04dea
-- name    : P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGG_act__a_200fb8f04dea
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:22:36.180646+00:00
-- url     : https://prove2.me/theorems/02b73f22-ce03-4e22-9e64-14d5162958f5
-- title:
--   P2 M Formalism Main Notions Moduli Integral Charts H1 Exp GG act  a 200fb8f04dea: P2 M Formalism Main Notions Moduli Integral Charts H1 Exp GG act  a 200fb8f04dea
-- statement:
--   The P2 M Formalism Main Notions Moduli Integral Charts H1 Exp GG act  a 200fb8f04dea construction uses the P2 M Formalism Main Notions Moduli Integral Charts H1 Exp GG act  a 200fb8f04dea property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/HasSubstActPS.lean#L92-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/HasSubstActPS.lean#L92-L101

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

theorem P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGG_act__a_200fb8f04dea {d : ℕ} {act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S}
    {φ : Fin d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S} (hφ : ∀ j, constantCoeff (φ j) = 0)
    (hact : ∀ a j, subst (fun p : Fin 1 × Fin d => φ p.2) (act a j) = subst (actPS (Dw := Dw) c a) (φ j))
    (a u : 𝓞 E) (j : Fin d) :
    subst (fun p : Fin 1 × Fin d => φa c φ u p.2) (act a j) = φa c φ (a * u) j := by sorry

alias «Formalism».«MainNotions».«ModuliIntegralCharts».«H1».«ExpGG».«act_φa» := P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGG_act__a_200fb8f04dea
