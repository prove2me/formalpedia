-- Prove2me | Theorems.Thm_P2M_GlobalTheory_FrameAdjSeries_jpt_trunc__a9b0999b8ded
-- name    : P2M_GlobalTheory_FrameAdjSeries_jpt_trunc__a9b0999b8ded
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:05:32.654836+00:00
-- url     : https://prove2.me/theorems/3ee5c334-cb5c-4523-8c24-fd4567a34edc
-- title:
--   P2 M Global Theory Frame Adj Series jpt trunc  a9b0999b8ded: P2 M Global Theory Frame Adj Series jpt trunc  a9b0999b8ded
-- statement:
--   The P2 M Global Theory Frame Adj Series jpt trunc  a9b0999b8ded construction uses the P2 M Global Theory Frame Adj Series jpt trunc  a9b0999b8ded property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsAdjointnessSeriesOfFrames.lean#L148-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsAdjointnessSeriesOfFrames.lean#L148-L155

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermCut
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermBGen
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermBPrim
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermBSer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsAdjointnessSeriesOfFrames
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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)
open GlobalTheory GlobalTheory.FrameAdjSeries
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermB Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} {t : SAB H X0}
variable {S : Type} [CommRing S] {x0 : Sp S ⟶ X0} {d : ℕ} {x : ∀ m, jOG x0 d m 1 ⟶ t.G}
variable {F : Fin d → MvPowerSeries (Fin 2 × Fin d) S} {act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S}
  {κ : Type} [Fintype κ] {tg : κ → (Sp (DualNumber S) ⟶ t.G.left)} {uvec : κ → Fin d → S}

theorem P2M_GlobalTheory_FrameAdjSeries_jpt_trunc__a9b0999b8ded (hch : IsChartG t x0 d F act tg uvec x) (m : ℕ) {n : ℕ} (i : Fin n) :
    homAt x0 (jetTrunc : Jet S (Fin n × Fin d) (m + 1) →ₐ[S] _) ≫ jptG t x0 d x (m + 1) i = jptG t x0 d x m i := by sorry

alias «GlobalTheory».«FrameAdjSeries».«jpt_trunc'» := P2M_GlobalTheory_FrameAdjSeries_jpt_trunc__a9b0999b8ded
