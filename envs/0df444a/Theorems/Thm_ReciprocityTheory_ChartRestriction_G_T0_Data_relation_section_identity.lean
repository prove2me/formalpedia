-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_relation_section_identity
-- name    : ReciprocityTheory.ChartRestriction.G.T0.Data.relation_section_identity
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T14:31:00.04537+00:00
-- url     : https://prove2.me/theorems/12aa4459-4a57-4211-8ac6-9cf6cfe8dde7
-- title:
--   Data: relation section identity
-- statement:
--   The Data construction uses the relation section identity property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/FZEqConstMulIrreduciblePow.lean#L26-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/FZEqConstMulIrreduciblePow.lean#L26-L72

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HtDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_BlockSphereProbIsProbabilityMeasure
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FZEqConstMulIrreduciblePow
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

theorem ReciprocityTheory.ChartRestriction.G.T0.Data.relation_section_identity (hd : d.AxH 𝒜) (c : ι) (i : Fin (d.D + 1)) :
    d.sH c (MvPolynomial.X (i, d.jc c)) + ∑ k ∈ Finset.univ.erase (d.jc c),
      d.sH c (MvPolynomial.X (i, k)) *
        algebraMap (Ω c) (OmS (Ω c) d.D d.N) (ratio (Ω := Ω c) (d.w k c) (d.w (d.jc c) c)) =
      if i = 0 then d.rationalBaseRow c else 0 := by sorry
