-- Prove2me | Theorems.Thm_P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_FrRatio_c__tr_5c2d9f8c1cdb
-- name    : P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_FrRatio_c__tr_5c2d9f8c1cdb
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T15:39:26.775882+00:00
-- url     : https://prove2.me/theorems/92cd6b7d-415c-4689-98f8-935c8f3ffa6b
-- title:
--   P2 M Formalism Main Notions Moduli Integral Charts H1 Fr Ratio c  tr 5c2d9f8c1cdb: P2 M Formalism Main Notions Moduli Integral Charts H1 Fr Ratio c  tr 5c2d9f8c1cdb
-- statement:
--   The P2 M Formalism Main Notions Moduli Integral Charts H1 Fr Ratio c  tr 5c2d9f8c1cdb construction uses the P2 M Formalism Main Notions Moduli Integral Charts H1 Fr Ratio c  tr 5c2d9f8c1cdb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/FrRatio.lean#L54-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/FrRatio.lean#L54-L63

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermBSer
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndFrFixAsm
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FrRatio
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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.FrRatio
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.GermD
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun Formalism.MainNotions.ModuliIntegralCharts.H1.GermB
attribute [local instance] Over.cartesianMonoidalCategory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} {t : SAB H X0}
variable {S : Type} [CommRing S] {x0 : Sp S ⟶ X0} {d : ℕ} {x : ∀ m, jOG x0 d m 1 ⟶ t.G}
variable {F : Fin d → MvPowerSeries (Fin 2 × Fin d) S} {act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S}
  {κ : Type} [Fintype κ] {tg : κ → (Sp (DualNumber S) ⟶ t.G.left)} {uvec : κ → Fin d → S}

theorem P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_FrRatio_c__tr_5c2d9f8c1cdb (hch : IsChartG t x0 d F act tg uvec x) (m : ℕ) (I : ULift.{0} (Finset (Fin 2))) :
    (homAt x0 (jetTrunc : Jet S (Fin 2 × Fin d) (m + 1) →ₐ[S] _)).left ≫
      cφG t ![jptG t x0 d x (m + 1) (0 : Fin 2), jptG t x0 d x (m + 1) (1 : Fin 2)] I =
      cφG t ![jptG t x0 d x m (0 : Fin 2), jptG t x0 d x m (1 : Fin 2)] I := by sorry

alias «Formalism».«MainNotions».«ModuliIntegralCharts».«H1».«FrRatio».«cφ_tr» := P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_FrRatio_c__tr_5c2d9f8c1cdb
