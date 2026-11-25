-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_dmap_injective
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.dmap_injective
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T10:05:15.533061+00:00
-- url     : https://prove2.me/theorems/6bc3cac9-94dd-4f27-89c1-3af682446740
-- title:
--   Arakelov Geometry: dmap injective
-- statement:
--   The Arakelov Geometry construction uses the dmap injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/NatCardEqPowLength.lean#L14-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/NatCardEqPowLength.lean#L14-L39

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsMultiHomogXpow
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_NatCardEqPowLength
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.dmap_injective {W : Ideal (MRing ι)} (hWp : W.IsPrime) (hWm : IsMultiHomogIdeal W)
    {i : ∀ k, ι k} (hi : ∀ k, (X ⟨k, i k⟩ : MRing ι) ∉ W) (a : K → ℕ) :
    Function.Injective (dmap W i a) := by sorry
