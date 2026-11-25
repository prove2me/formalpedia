-- Prove2me | Theorems.Thm_P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGI_ptm__L_8c0085973b4b
-- name    : P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGI_ptm__L_8c0085973b4b
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T00:02:38.902343+00:00
-- url     : https://prove2.me/theorems/612c7eb0-de40-44c9-9776-296ca17741b1
-- title:
--   P2 M Formalism Main Notions Moduli Integral Charts H1 Exp GI ptm  L 8c0085973b4b: P2 M Formalism Main Notions Moduli Integral Charts H1 Exp GI ptm  L 8c0085973b4b
-- statement:
--   The P2 M Formalism Main Notions Moduli Integral Charts H1 Exp GI ptm  L 8c0085973b4b construction uses the P2 M Formalism Main Notions Moduli Integral Charts H1 Exp GI ptm  L 8c0085973b4b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/GmHomAt.lean#L35-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/GmHomAt.lean#L35-L64

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpChartActionPoint
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GmHomAt
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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGI
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGU Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGF Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGG Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGH
attribute [local instance] Over.cartesianMonoidalCategory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {S : Type} [CommRing S] [Algebra c.F S] [Algebra ℚ S] {y : FrPt Xo c S}

theorem P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGI_ptm__L_8c0085973b4b (C : ChartAt Xo c y) (φ : Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S)
    (hφ : ∀ j, MvPowerSeries.constantCoeff (φ j) = 0)
    (hact : ∀ a j, MvPowerSeries.subst (fun p : Fin 1 × Fin C.d => φ p.2) (C.B.A.act a j) =
      MvPowerSeries.subst (actPS (Dw := Dw) c a) (φ j)) (m : ℕ) (k : 𝓞 E) :
    ptm C ![φa c φ k] m ≫ homAt y.x (jetSubstP m (σL C m)) = ptm C ![φa c φ k, φa c φ (H.w0 * k)] m := by sorry

alias «Formalism».«MainNotions».«ModuliIntegralCharts».«H1».«ExpGI».«ptm_σL» := P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGI_ptm__L_8c0085973b4b
