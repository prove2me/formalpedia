-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_AH_smul
-- name    : ReciprocityTheory.ChartRestriction.G.T0.Data.AH_smul
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T17:24:38.342175+00:00
-- url     : https://prove2.me/theorems/5d8361d5-6d6c-5289-8aed-a5e1f6da6d1a
-- title:
--   Data: AH smul
-- statement:
--   The Data construction uses the AH smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/HHINDD.lean#L19-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/HHINDD.lean#L19-L94

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HHINDC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HHINDD
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.Closed MeasureTheory IsDedekindDomain
  ReciprocityTheory.ChartRestriction.G.T0.HeightMultiplicativity
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}
open ReciprocityTheory.ChartRestriction.G.T0.Data
variable (d : Data K ι Ω WT A)

theorem ReciprocityTheory.ChartRestriction.G.T0.Data.AH_smul (hd : d.AxH 𝒜) (h : d.S1) (O : ∀ c, AddValuation (Ω c) (WithTop ℤ) → A c → ℤ)
    (Nr : ∀ c, A c → (Ω c →+* ℂ) → ℝ) (ta : ∀ c, A c) (a : ∀ c, Ω c) (ha : ∀ c, a c ≠ 0)
    (hOs : ∀ c v, d.admitted c v →
      ((O c v (a c • ta c) : ℤ) : WithTop ℤ) = v (a c) + (O c v (ta c) : WithTop ℤ))
    (hOf : ∀ c, {v | d.admitted c v ∧ O c v (ta c) ≠ 0}.Finite)
    (hOf' : ∀ c, {v | d.admitted c v ∧ O c v (a c • ta c) ≠ 0}.Finite)
    (hPf : ∀ c, {p | p ∈ d.HtOne ∧ d.anP h O c (ta c) p ≠ 0}.Finite)
    (hNs : ∀ c P, Nr c (a c • ta c) P = ‖P (a c)‖ * Nr c (ta c) P)
    (hN0 : ∀ c P, Nr c (ta c) P ≠ 0)
    (hI : ∀ c sg, Integrable (d.aI Nr c (ta c) sg) (blockSphereProb d.D (d.N + 1)))
    (hI' : ∀ c sg, Integrable (d.aI Nr c (a c • ta c) sg) (blockSphereProb d.D (d.N + 1))) :
    d.AH h O Nr (fun c => a c • ta c) = d.AH h O Nr ta := by sorry
