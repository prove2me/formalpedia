-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_bGram_change
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.bGram_change
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T10:03:11.149745+00:00
-- url     : https://prove2.me/theorems/efc5ac2a-5e12-5a73-bd88-a4b1934bd5f7
-- title:
--   Arakelov Geometry: b Gram change
-- statement:
--   The Arakelov Geometry construction uses the b Gram change property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/ABridgeSt.lean#L229-L248
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/ABridgeSt.lean#L229-L248

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsBergDensity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_SectionModuleEqSpanPow
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AParamSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ABridgeStA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ABridgeStB
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_PluriharmonicAnalysis_BergmanDerivSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ABridgeSt
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
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.GeometryOfNumbersTheory MvPolynomial MeasureTheory Module Filter Asymptotics
open scoped ComplexOrder
variable {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ] {D : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.bGram_change {J : Type} {μ : Measure (J → ℂ)} {r : ℕ} (s s' : Fin r → (J → ℂ) → ℂ)
    (w : (J → ℂ) → ℝ) (A : Matrix (Fin r) (Fin r) ℤ)
    (hint : ∀ i j, Integrable (fun z => starRingEnd ℂ (s i z) * s j z * (w z : ℂ)) μ)
    (hs : ∀ k, s' k =ᵐ[μ] fun z => ∑ l, (A k l : ℂ) * s l z) :
    bGram μ s' w = A.map (Int.cast : ℤ → ℂ) * bGram μ s w * (A.map (Int.cast : ℤ → ℂ)).transpose := by sorry
