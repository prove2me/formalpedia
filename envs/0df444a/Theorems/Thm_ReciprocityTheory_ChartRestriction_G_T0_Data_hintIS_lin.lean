-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_hintIS_lin
-- name    : ReciprocityTheory.ChartRestriction.G.T0.Data.hintIS_lin
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-27T04:52:24.059496+00:00
-- url     : https://prove2.me/theorems/2b198330-e047-4bf2-926a-3f95fc636be9
-- title:
--   Data: hint IS lin
-- statement:
--   The Data construction uses the hint IS lin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/HintISBounds.lean#L35-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/HintISBounds.lean#L35-L48

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HintLogFinprod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HintISBounds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField MeasureTheory ReciprocityTheory.MultiplicativeHeights
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}
open ReciprocityTheory.ChartRestriction.G.T0.Data
variable (d : Data K ι Ω WT A)

theorem ReciprocityTheory.ChartRestriction.G.T0.Data.hintIS_lin (hd : d.AxH 𝒜) (h : d.S1) {c : ι} {sg : K →+* ℂ}
    {φ₁ φ₂ : (Ω c →+* ℂ) → ℝ} (h₁ : d.HintIS c sg φ₁) (h₂ : d.HintIS c sg φ₂) (a₁ a₂ b : ℝ) :
    d.HintIS c sg (fun P => a₁ * φ₁ P + a₂ * φ₂ P + b) := by sorry
