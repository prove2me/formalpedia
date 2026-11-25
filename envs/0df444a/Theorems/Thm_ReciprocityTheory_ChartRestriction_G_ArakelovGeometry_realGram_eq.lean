-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_realGram_eq
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.realGram_eq
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T10:14:06.292131+00:00
-- url     : https://prove2.me/theorems/39d40ec1-a684-5c80-949a-c27127124750
-- title:
--   Arakelov Geometry: real Gram eq
-- statement:
--   The Arakelov Geometry construction uses the real Gram eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/ABridgeStA.lean#L105-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/ABridgeStA.lean#L105-L127

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsBergDensity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_LemCone
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ABridgeStA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.GeometryOfNumbersTheory MvPolynomial MeasureTheory Module
variable {Ω : Type} [Field Ω] [CharZero Ω] {J : Type} [Fintype J]

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.realGram_eq (m : ConeMetric ℂ J) (μ : Measure (J → ℂ)) (n : ℕ) {r : ℕ}
    (b : Fin r → MvPolynomial J ℚ) (k l : Fin r) :
    realGram (K := ℚ) (fun _ => m) (fun _ => μ) n b k l =
      (bGram μ (fun k => secFun (b k)) (wgt m n) k l).re := by sorry
