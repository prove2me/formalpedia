-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_good_primes_properties
-- name    : ReciprocityTheory.ChartRestriction.G.T0.Data.good_primes_properties
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T15:13:32.336252+00:00
-- url     : https://prove2.me/theorems/e53249d7-71de-47b1-abe9-64b3070f4a53
-- title:
--   Data: good primes properties
-- statement:
--   The Data construction uses the good primes properties property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/GoodPrimesProperties.lean#L20-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/GoodPrimesProperties.lean#L20-L92

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HtDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_UniformizerOfResidueIndep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AdmissibleValuationPrimeUnique
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GoodPrimesProperties
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_AdmissibleValuationPrimeUnique

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

theorem ReciprocityTheory.ChartRestriction.G.T0.Data.good_primes_properties (hd : d.AxH 𝒜) (h : d.S1) (c : ι) :
    (∀ v : AddValuation (Ω c) (WithTop ℤ), d.admitted c v → IsTrivOn K v →
      {p | p ∈ d.HtOne ∧ ∃ w ∈ d.GoodP c p, d.Wres c w = v}.Subsingleton) ∧
    (∀ p ∈ d.HtOne, (∃ w, w ∈ d.GoodP c p) →
      ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous (fun b : Fin (d.D + 1) => if b = 0 then 0 else d.dg (d.gen p))
        (d.gen p)) ∧
    (∀ (G : WT) (ta : A c), ta ∈ 𝒜 c G → ta ≠ 0 →
      {p | p ∈ d.HtOne ∧ d.nP h c G ta p ≠ 0}.Finite) ∧
    (∀ ta : A c, ta ∈ 𝒜 c d.wL → ta ≠ 0 → {p | p ∈ d.HtOne ∧ d.nPMM h c ta p ≠ 0}.Finite) := by sorry
