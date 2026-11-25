-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_sigF_algebraMap
-- name    : ReciprocityTheory.ChartRestriction.G.T0.Data.sigF_algebraMap
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T15:28:36.812919+00:00
-- url     : https://prove2.me/theorems/b149a33c-5a17-49b2-ad39-218a1d7a1b44
-- title:
--   Data: sig F algebra Map
-- statement:
--   The Data construction uses the sig F algebra Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/ProdZpowEqZpowSum.lean#L189-L193
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/ProdZpowEqZpowSum.lean#L189-L193

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_BlockDegOfScale
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GoodPrimesProperties
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_KTFiniteDimensional
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ProdZpowEqZpowSum
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

theorem ReciprocityTheory.ChartRestriction.G.T0.Data.sigF_algebraMap (b : Fin (d.D + 1)) (u : Kˣ) (g : KTp K d.D d.N) :
    sigF (K := K) (D := d.D) (N := d.N) b u (algebraMap (KTp K d.D d.N) (KTf K d.D d.N) g) =
      algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (sigP b u g) := by sorry
