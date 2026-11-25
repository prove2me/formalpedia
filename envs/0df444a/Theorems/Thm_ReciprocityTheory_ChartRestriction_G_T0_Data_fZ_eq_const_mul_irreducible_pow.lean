-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_fZ_eq_const_mul_irreducible_pow
-- name    : ReciprocityTheory.ChartRestriction.G.T0.Data.fZ_eq_const_mul_irreducible_pow
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T14:29:37.63136+00:00
-- url     : https://prove2.me/theorems/da997b2f-d5f1-5a57-acfa-a1aacdec149c
-- title:
--   Data: f Z eq const mul irreducible pow
-- statement:
--   The Data construction uses the f Z eq const mul irreducible pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/FZEqConstMulIrreduciblePow.lean#L183-L247
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/FZEqConstMulIrreduciblePow.lean#L183-L247

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

theorem ReciprocityTheory.ChartRestriction.G.T0.Data.fZ_eq_const_mul_irreducible_pow (hd : d.AxH 𝒜) (h : d.S1) (c : ι) (F : KTp K d.D d.N)
    (hF : algebraMap (KTp K d.D d.N) (KTf K d.D d.N) F = d.fZ h c)
    (hpos : 0 < ReciprocityTheory.MultiplicativeHeights.h0 F) :
    ∃ (F0 : KTp K d.D d.N) (κ : K) (m : ℕ), κ ≠ 0 ∧ 1 ≤ m ∧ Irreducible F0 ∧
      F = MvPolynomial.C κ * F0 ^ m ∧
      ∀ Q : KTp K d.D d.N, d.relationEliminateColumn c Q = 0 ↔ F0 ∣ Q := by sorry
