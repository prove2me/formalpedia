-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_fib
-- name    : ReciprocityTheory.ChartRestriction.G.T0.Data.fib
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T10:36:07.086807+00:00
-- url     : https://prove2.me/theorems/e12eeaed-b042-51ca-a4fd-30206d799211
-- title:
--   Data: fib
-- statement:
--   The Data construction uses the fib property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/HNormPtsB.lean#L40-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/HNormPtsB.lean#L40-L88

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HNormDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_CastAddNeNatAdd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_SacSuccAbove
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HNormPtsB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField MvPolynomial MeasureTheory
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}
open ReciprocityTheory.ChartRestriction.G.T0.Data
variable (d : Data K ι Ω WT A)

theorem ReciprocityTheory.ChartRestriction.G.T0.Data.fib (hd : d.AxH 𝒜) (h : d.S1) (c : ι) (sg : K →+* ℂ) (t : Fin d.D → Fin (d.N + 1) → ℂ)
    (y : Fin (d.N + 1 + d.D) → ℂ)
    (hpt : ∀ q : MvPolynomial (TVar d.D d.N) K, q ≠ 0 →
      eval₂ sg (NPB.gpt (fun q => t q.1 q.2) y) q ≠ 0) :
    letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
    (d.ST c sg t).Finite ∧ (d.ST c sg t).ncard = d.delc c ∧
      (∀ g : Ω c, tauPev sg _ hpt (Algebra.norm (KTf K d.D d.N) (algebraMap (Ω c) (OmS (Ω c) d.D d.N) g))
        = ∏ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg t), P g) ∧
      tauPev sg _ hpt (Algebra.norm (KTf K d.D d.N) (d.rationalBaseRow c)) =
        ∏ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg t),
          ∑ j, y (Fin.castAdd d.D j) * P (ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c)) := by sorry
