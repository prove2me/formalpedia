-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_ordMinMax_nonneg
-- name    : ReciprocityTheory.ChartRestriction.G.T0.Data.ordMinMax_nonneg
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-27T05:47:41.750103+00:00
-- url     : https://prove2.me/theorems/70f29aab-7d49-4ba5-8be8-1ac5fc257c68
-- title:
--   Data: ord Min Max nonneg
-- statement:
--   The Data construction uses the ord Min Max nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/HeightProdPowMultiHomogeneous.lean#L113-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/HeightProdPowMultiHomogeneous.lean#L113-L134

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValuationGenericRatioEqRestriction
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GeneratorNeZeroOfHeight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HeightProdPowMultiHomogeneous
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField ReciprocityTheory.MultiplicativeHeights
open ReciprocityTheory.ChartRestriction.G.T0.Data
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}
variable (d : Data K ι Ω WT A)

theorem ReciprocityTheory.ChartRestriction.G.T0.Data.ordMinMax_nonneg (hd : d.AxH 𝒜) (h : d.S1) (x : Fin (d.N + 1) → K) (c : ι)
    (hx : d.wx x c ≠ 0) {p : Ideal (KTp K d.D d.N)} (hp : p ∈ d.HtOne)
    {w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)} (hw : w ∈ d.GoodP c p) :
    0 ≤ d.ordMM c (d.Wres c w) (d.wx x c) := by sorry
