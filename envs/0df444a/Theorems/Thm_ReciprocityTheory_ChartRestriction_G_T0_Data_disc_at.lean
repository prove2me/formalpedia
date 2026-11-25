-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_disc_at
-- name    : ReciprocityTheory.ChartRestriction.G.T0.Data.disc_at
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T14:19:41.44573+00:00
-- url     : https://prove2.me/theorems/e985fadc-e684-4f3a-a20b-c123aa3e764e
-- title:
--   Data: disc at
-- statement:
--   The Data construction uses the disc at property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/HDiscAG.lean#L28-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/HDiscAG.lean#L28-L112

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GenericSectionOfAxioms
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscAB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscAF
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscAG
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField IsDedekindDomain
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}
open ReciprocityTheory.ChartRestriction.G.T0.Data
variable (d : Data K ι Ω WT A)

theorem ReciprocityTheory.ChartRestriction.G.T0.Data.disc_at (hd : d.AxH 𝒜) (h : d.S1) (la : HeightOneSpectrum (𝓞 K)) :
    ∃ n t : ℕ, ∃ N : ℤ, (d.htOf hd h).Ila la = n ∧ d.NlaG h d.wF hd.a4.choose la = N ∧
      ∃ u : Op d.D d.N la, IsUnit u ∧ d.De hd h =
        (algebraMap K (KTf K d.D d.N) ((unif la : 𝓞 K) : K)) ^ (((2 * n + t : ℕ) : ℤ) - 2 * N) *
          OpToKT d.D d.N la u := by sorry
