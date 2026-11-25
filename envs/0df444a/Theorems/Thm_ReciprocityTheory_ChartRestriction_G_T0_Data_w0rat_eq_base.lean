-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_w0rat_eq_base
-- name    : ReciprocityTheory.ChartRestriction.G.T0.Data.w0rat_eq_base
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T14:14:16.604965+00:00
-- url     : https://prove2.me/theorems/d3f7596c-dd5c-418e-9667-4f8dd65dad90
-- title:
--   Data: w0rat eq base
-- statement:
--   The Data construction uses the w0rat eq base property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/KerPLeOfPlace.lean#L134-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/KerPLeOfPlace.lean#L134-L154

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GeneratorNeZeroOfHeight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ScaleMultiHomogeneous
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_KerPLeOfPlace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField MvPolynomial
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}
open ReciprocityTheory.ChartRestriction.G.T0.Data
variable (d : Data K ι Ω WT A)

theorem ReciprocityTheory.ChartRestriction.G.T0.Data.w0rat_eq_base (hd : d.AxH 𝒜) (c : ι) :
    d.rationalBaseRow c = algebraMap (MvPolynomial (SVar d.D d.N) (Ω c)) (OmS (Ω c) d.D d.N)
      (X (Sum.inl ()) + ∑ k, X (Sum.inr ((0 : Fin (d.D + 1)), k)) * C (d.x c k)) := by sorry
