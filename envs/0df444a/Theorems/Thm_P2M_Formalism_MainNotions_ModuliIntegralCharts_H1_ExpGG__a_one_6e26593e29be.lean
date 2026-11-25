-- Prove2me | Theorems.Thm_P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGG__a_one_6e26593e29be
-- name    : P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGG__a_one_6e26593e29be
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T00:05:21.441215+00:00
-- url     : https://prove2.me/theorems/c48d457d-489d-4486-84be-854f16e4b527
-- title:
--   P2 M Formalism Main Notions Moduli Integral Charts H1 Exp GG  a one 6e26593e29be: P2 M Formalism Main Notions Moduli Integral Charts H1 Exp GG  a one 6e26593e29be
-- statement:
--   The P2 M Formalism Main Notions Moduli Integral Charts H1 Exp GG  a one 6e26593e29be construction uses the P2 M Formalism Main Notions Moduli Integral Charts H1 Exp GG  a one 6e26593e29be property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/HasSubstActPS.lean#L38-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/HasSubstActPS.lean#L38-L43

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

theorem P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGG__a_one_6e26593e29be {d : ℕ} (φ : Fin d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S) : φa c φ 1 = φ := by sorry

alias «Formalism».«MainNotions».«ModuliIntegralCharts».«H1».«ExpGG».«φa_one» := P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGG__a_one_6e26593e29be
