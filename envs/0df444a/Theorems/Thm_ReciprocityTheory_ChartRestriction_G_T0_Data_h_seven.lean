-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_h_seven
-- name    : ReciprocityTheory.ChartRestriction.G.T0.Data.h_seven
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-27T05:58:39.127215+00:00
-- url     : https://prove2.me/theorems/f1ba8fc9-df6c-5e6e-9515-4374ac73d0d8
-- title:
--   Data: h seven
-- statement:
--   The Data construction uses the h seven property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/HSeven.lean#L22-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/HSeven.lean#L22-L88

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HtDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_CardEmbPos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HFour
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_IntNsg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FsumLeOf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HSeven
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}
open ReciprocityTheory.ChartRestriction.G.T0.Data
variable (d : Data K ι Ω WT A)

theorem ReciprocityTheory.ChartRestriction.G.T0.Data.h_seven (hd : d.AxH 𝒜) (h : d.S1) (hH1 : d.FinitePlaceHyp) (hF1d : d.TrivialPlaceHyp) (hSup : d.HtSup)
    (hI2be : d.HeightIntegralBoundEstimate) (x : Fin (d.N + 1) → K) (hx : ∀ c, d.wx x c ≠ 0) (ta' : ∀ c, A c)
    (hta' : ∀ c, ta' c ∈ 𝒜 c d.wF ∧ ta' c ≠ 0) :
    let lr := Real.log (d.N + 1 : ℕ) + 1 / 2
    let HL := d.Hgt h d.wL (d.wx x)
    let Hde := d.Hgt h (d.n1 • d.wde) d.et / d.n1
    let ade := (d.aG h (d.n1 • d.wde) d.et : ℝ) / d.n1
    let aG1 := (d.aG h ((2 : ℕ) • d.G1) d.ta1 : ℝ) / 2
    let X8 := d.HgtMM h (d.wx x) + d.del * ((∑ᶠ la, d.nu la * logNorm la) /
      (Module.finrank ℚ K : ℝ) + d.tableLineDegreeFive * d.DF + d.cc * d.tableLineDegreeTwo) + d.D * d.cc * d.g0 * ade * lr
    let Y := d.del * d.PI4 * d.D * d.wsize d.wL + d.D * aG1 * lr
    HL ≤ X8 + d.cc * d.g0 * Hde ∧ Hde ≤ HL + Y ∧
      d.Hgt h d.wF ta' ≤ (d.D + 4) * HL + d.del * d.PI4 * d.D * d.wsize d.wL +
        d.D * d.aG h d.G2 d.ta2 * lr := by sorry
