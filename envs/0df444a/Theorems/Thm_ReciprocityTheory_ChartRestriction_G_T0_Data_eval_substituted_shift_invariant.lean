-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_eval_substituted_shift_invariant
-- name    : ReciprocityTheory.ChartRestriction.G.T0.Data.eval_substituted_shift_invariant
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-27T05:47:57.180227+00:00
-- url     : https://prove2.me/theorems/db093aef-3ff1-486b-a9fa-cfde688907c5
-- title:
--   Data: eval substituted shift invariant
-- statement:
--   The Data construction uses the eval substituted shift invariant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/SphereMeanSubstitutedEqIntegral.lean#L32-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/SphereMeanSubstitutedEqIntegral.lean#L32-L44

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HeightProdPowMultiHomogeneous
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HintLogFinprod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_SphereMeanSubstitutedEqIntegral
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

theorem ReciprocityTheory.ChartRestriction.G.T0.Data.eval_substituted_shift_invariant (x : Fin (d.N + 1) → K) (F : KTp K d.D d.N) (sg : K →+* ℂ)
    (t0 : Fin (d.N + 1) → ℂ) (z : BlockSphere d.D (d.N + 1)) :
    MvPolynomial.eval (hintPt t0 z) (MvPolynomial.map sg (d.translatedForm x F)) =
      MvPolynomial.eval (hintPt 0 z) (MvPolynomial.map sg (d.translatedForm x F)) := by sorry
