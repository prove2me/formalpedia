-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_eval_substituted_eq_eval_update
-- name    : ReciprocityTheory.ChartRestriction.G.T0.Data.eval_substituted_eq_eval_update
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-27T05:47:55.785849+00:00
-- url     : https://prove2.me/theorems/75d82226-605e-4ebd-b8fa-da6a3ea0815c
-- title:
--   Data: eval substituted eq eval update
-- statement:
--   The Data construction uses the eval substituted eq eval update property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/SphereMeanSubstitutedEqIntegral.lean#L19-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/SphereMeanSubstitutedEqIntegral.lean#L19-L30

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

theorem ReciprocityTheory.ChartRestriction.G.T0.Data.eval_substituted_eq_eval_update (x : Fin (d.N + 1) → K) (F : KTp K d.D d.N) (sg : K →+* ℂ)
    (y : Fin (d.D + 1) × Fin (d.N + 1) → ℂ) :
    MvPolynomial.eval y (MvPolynomial.map sg (d.translatedForm x F)) =
      MvPolynomial.eval (fun v => if v.1 = 0 then sg (x v.2) else y v) (MvPolynomial.map sg F) := by sorry
