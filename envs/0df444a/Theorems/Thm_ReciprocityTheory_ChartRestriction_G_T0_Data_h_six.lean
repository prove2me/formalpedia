-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_h_six
-- name    : ReciprocityTheory.ChartRestriction.G.T0.Data.h_six
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-27T04:54:04.69323+00:00
-- url     : https://prove2.me/theorems/5051502d-42bc-5141-935b-462c8337c651
-- title:
--   Data: h six
-- statement:
--   The Data construction uses the h six property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/HSix.lean#L21-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/HSix.lean#L21-L134

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HtDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_UniformizerOfResidueIndep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GoodPrimesProperties
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FsumLeOf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HSix
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

theorem ReciprocityTheory.ChartRestriction.G.T0.Data.h_six (hd : d.AxH 𝒜) (h : d.S1) (hF1d : d.TrivialPlaceHyp) (x : Fin (d.N + 1) → K)
    (hx : ∀ c, d.wx x c ≠ 0) (ta' : ∀ c, A c) (hta' : ∀ c, ta' c ∈ 𝒜 c d.wF ∧ ta' c ≠ 0) :
    (d.aG h d.wL (d.wx x) : ℝ) ≤ 4 / 3 * d.del ∧
    0 ≤ d.aG h (d.n1 • d.wde) d.et ∧ d.aG h (d.n1 • d.wde) d.et ≤ d.n1 * d.aG h d.wL (d.wx x) ∧
    0 ≤ d.aG h ((2 : ℕ) • d.G1) d.ta1 ∧ d.aG h ((2 : ℕ) • d.G1) d.ta1 ≤ 2 * d.aG h d.wL (d.wx x) ∧
    0 ≤ d.aG h d.wF ta' ∧ d.aG h d.wF ta' ≤ (d.D + 4) * d.aG h d.wL (d.wx x) ∧
    0 ≤ d.aG h d.G2 d.ta2 ∧ d.aG h d.G2 d.ta2 ≤ (d.D + 4) * d.aG h d.wL (d.wx x) := by sorry
