-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_pf_fin
-- name    : ReciprocityTheory.ChartRestriction.G.T0.Data.pf_fin
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T14:36:46.712145+00:00
-- url     : https://prove2.me/theorems/dfc9731d-cf3b-4c86-b2a5-dd0132ff7f06
-- title:
--   Data: pf fin
-- statement:
--   The Data construction uses the pf fin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/HHINDA.lean#L224-L285
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/HHINDA.lean#L224-L285

import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusL2CauchyInequality
import Definitions.Def_ReciprocityTheory_SemistableReduction_LagrangeIdealLiftsFact
import Definitions.Def_ReciprocityTheory_SemistableReduction_RestBlockSubstIsMultiHomogeneous
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HNormPts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HHINDA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights IsDedekindDomain ReciprocityTheory.ChartRestriction.G.T0.HeightMultiplicativity
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}
open ReciprocityTheory.ChartRestriction.G.T0.Data
variable (d : Data K ι Ω WT A)

theorem ReciprocityTheory.ChartRestriction.G.T0.Data.pf_fin (hd : d.AxH 𝒜) (h : d.S1) (c : ι) (y : OmS (Ω c) d.D d.N) (hy : y ≠ 0)
    (PA PB : KTp K d.D d.N) (hA : PA ≠ 0) (hB : PB ≠ 0)
    (hAB : letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
      Algebra.norm (KTf K d.D d.N) y * algebraMap (KTp K d.D d.N) (KTf K d.D d.N) PB =
        algebraMap (KTp K d.D d.N) (KTf K d.D d.N) PA)
    (la : HeightOneSpectrum (𝓞 K)) :
    Real.log (gaussAbs (FinitePlace.mk la) PA) - Real.log (gaussAbs (FinitePlace.mk la) PB) =
      -((d.nLa h c la y : ℝ) * logNorm la) := by sorry
