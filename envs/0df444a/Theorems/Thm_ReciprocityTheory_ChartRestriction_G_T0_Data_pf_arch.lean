-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_pf_arch
-- name    : ReciprocityTheory.ChartRestriction.G.T0.Data.pf_arch
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T15:50:39.587877+00:00
-- url     : https://prove2.me/theorems/27782e78-e396-468b-81f9-309eb521d259
-- title:
--   Data: pf arch
-- statement:
--   The Data construction uses the pf arch property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/HHINDB.lean#L39-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/HHINDB.lean#L39-L103

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HHINDA
import Definitions.Def_ReciprocityTheory_SemistableReduction_AeBlockSphereEvalNeZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_NormByPlaces
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GoodPrimesProperties
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_NormFactorizationClause
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HHINDB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.Closed MeasureTheory ReciprocityTheory.ChartRestriction.G.T0.HeightMultiplicativity
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}
open ReciprocityTheory.ChartRestriction.G.T0.Data
variable (d : Data K ι Ω WT A)

theorem ReciprocityTheory.ChartRestriction.G.T0.Data.pf_arch (hd : d.AxH 𝒜) (h : d.S1) (c : ι) (a : Ω c) (ha : a ≠ 0)
    (PA PB : KTp K d.D d.N) (hA : PA ≠ 0) (hB : PB ≠ 0) (eA eB : Fin (d.D + 1) → ℕ)
    (hAm : IsMultiHomogeneous eA PA) (hBm : IsMultiHomogeneous eB PB)
    (hAB : letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
      Algebra.norm (KTf K d.D d.N) (algebraMap (Ω c) (OmS (Ω c) d.D d.N) a) *
        algebraMap (KTp K d.D d.N) (KTf K d.D d.N) PB =
        algebraMap (KTp K d.D d.N) (KTf K d.D d.N) PA)
    (sg : K →+* ℂ) :
    blockSphereMean (d.D + 1) (d.N + 1) (MvPolynomial.map sg PA) -
      blockSphereMean (d.D + 1) (d.N + 1) (MvPolynomial.map sg PB) =
      ∫ z, d.lsum c sg a z ∂(blockSphereProb d.D (d.N + 1)) := by sorry
