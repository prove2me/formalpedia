-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_conj_bGram
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.conj_bGram
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T10:05:12.359557+00:00
-- url     : https://prove2.me/theorems/95f0afbd-5d3b-5e80-af66-b1a2db30483a
-- title:
--   Arakelov Geometry: conj b Gram
-- statement:
--   The Arakelov Geometry construction uses the conj b Gram property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/ABridgeStA.lean#L90-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/ABridgeStA.lean#L90-L103

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

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.conj_bGram {m : ConeMetric ℂ J} {μ : Measure (J → ℂ)} (hm : IsConjInvariant m)
    (hμ : μ.map conjPt = μ) (n : ℕ) {r : ℕ} (b : Fin r → MvPolynomial J ℚ) (i j : Fin r) :
    starRingEnd ℂ (bGram μ (fun k => secFun (b k)) (wgt m n) i j) =
      bGram μ (fun k => secFun (b k)) (wgt m n) i j := by sorry
