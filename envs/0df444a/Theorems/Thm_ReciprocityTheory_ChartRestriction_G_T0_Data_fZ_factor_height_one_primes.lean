-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_fZ_factor_height_one_primes
-- name    : ReciprocityTheory.ChartRestriction.G.T0.Data.fZ_factor_height_one_primes
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T15:45:04.759241+00:00
-- url     : https://prove2.me/theorems/735608b4-7f65-4ee7-a9f0-0bd96d028334
-- title:
--   Data: f Z factor height one primes
-- statement:
--   The Data construction uses the f Z factor height one primes property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/FZMultiHomogeneousDegreeSum.lean#L57-L179
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/FZMultiHomogeneousDegreeSum.lean#L57-L179

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ProdZpowEqZpowSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_KerPLeOfPlace
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FZMultiHomogeneousDegreeSum
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

theorem ReciprocityTheory.ChartRestriction.G.T0.Data.fZ_factor_height_one_primes (hd : d.AxH 𝒜) (h : d.S1) (c : ι) (F : KTp K d.D d.N)
    (hF : algebraMap (KTp K d.D d.N) (KTf K d.D d.N) F = d.fZ h c) :
    ∃ κ : K, κ ≠ 0 ∧ ∃ T : Finset (Ideal (KTp K d.D d.N)), ∃ e : Ideal (KTp K d.D d.N) → ℕ,
      (∀ p ∈ T, p ∈ d.HtOne) ∧ F = C κ * ∏ p ∈ T, d.gen p ^ e p ∧
      ∀ p ∈ T, e p ≠ 0 → ∃ w ∈ d.OverP c p, (∀ a : Ω c, a ≠ 0 → d.Wres c w a = 0) ∧
        0 < w (d.rationalBaseRow c) := by sorry
