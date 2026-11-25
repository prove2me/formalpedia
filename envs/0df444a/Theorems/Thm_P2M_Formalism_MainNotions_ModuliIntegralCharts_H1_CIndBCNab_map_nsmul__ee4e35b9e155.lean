-- Prove2me | Theorems.Thm_P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_CIndBCNab_map_nsmul__ee4e35b9e155
-- name    : P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_CIndBCNab_map_nsmul__ee4e35b9e155
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:59:14.107981+00:00
-- url     : https://prove2.me/theorems/b4ebc5b9-5f68-4100-99ad-3370e7db2492
-- title:
--   P2 M Formalism Main Notions Moduli Integral Charts H1 CInd BCNab map nsmul  ee4e35b9e155: P2 M Formalism Main Notions Moduli Integral Charts H1 CInd BCNab map nsmul  ee4e35b9e155
-- statement:
--   The P2 M Formalism Main Notions Moduli Integral Charts H1 CInd BCNab map nsmul  ee4e35b9e155 construction uses the P2 M Formalism Main Notions Moduli Integral Charts H1 CInd BCNab map nsmul  ee4e35b9e155 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/CIndBCNab.lean#L41-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/CIndBCNab.lean#L41-L44

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndBC
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndBCNab
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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.CIndBCNab
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {S S' : Type} [CommRing S] [CommRing S'] (ψ : S →+* S') {d : ℕ}

theorem P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_CIndBCNab_map_nsmul__ee4e35b9e155 {σ : Type} (k : ℕ) (g : MvPowerSeries σ S) :
    map ψ ((k : S) • g) = (k : S') • map ψ g := by sorry

alias «Formalism».«MainNotions».«ModuliIntegralCharts».«H1».«CIndBCNab».«map_nsmul'» := P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_CIndBCNab_map_nsmul__ee4e35b9e155
