-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_hint_log_le
-- name    : ReciprocityTheory.ChartRestriction.G.T0.Data.hint_log_le
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-27T04:50:51.410204+00:00
-- url     : https://prove2.me/theorems/9758ad35-655c-5348-b83e-068f1a64e212
-- title:
--   Data: hint log le
-- statement:
--   The Data construction uses the hint log le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/HintISBounds.lean#L188-L190
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/HintISBounds.lean#L188-L190

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

theorem ReciprocityTheory.ChartRestriction.G.T0.Data.hint_log_le (hd : d.AxH 𝒜) {c : ι} {G : WT} {f : A c} (hf : f ∈ 𝒜 c G) (hf0 : f ≠ 0)
    {sg : K →+* ℂ} {B : ℝ} (hB : ∀ P ∈ PT (Ω := Ω c) sg, d.nrm c G f P ≤ B) :
    ∀ P ∈ PT (Ω := Ω c) sg, Real.log (d.nrm c G f P) ≤ Real.log B := by sorry
