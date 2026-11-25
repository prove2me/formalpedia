-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_genericHomAt_relation
-- name    : ReciprocityTheory.ChartRestriction.G.T0.Data.genericHomAt_relation
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T10:36:13.913724+00:00
-- url     : https://prove2.me/theorems/0e3ce72d-8bfa-449b-a55e-1ab5622778df
-- title:
--   Data: generic Hom At relation
-- statement:
--   The Data construction uses the generic Hom At relation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/ValAlgebraMapEqZero.lean#L212-L278
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/ValAlgebraMapEqZero.lean#L212-L278

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HtDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraicIndependentResidueOfIsUnit
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValAlgebraMapEqZero
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

theorem ReciprocityTheory.ChartRestriction.G.T0.Data.genericHomAt_relation (hd : d.AxH 𝒜) (c : ι) (j0 : Fin (d.N + 1)) (hw0 : d.w j0 c ≠ 0)
    (hq : ∀ j, ratio (Ω := Ω c) (d.w j c) (d.w j0 c) =
      ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c) / ratio (Ω := Ω c) (d.w j0 c) (d.w (d.jc c) c))
    (i : Fin (d.D + 1)) (hi : i ≠ 0) :
    d.sH c (X (i, j0)) = -∑ j ∈ Finset.univ.erase j0, d.sH c (X (i, j)) *
      algebraMap (Ω c) (OmS (Ω c) d.D d.N) (ratio (Ω := Ω c) (d.w j c) (d.w j0 c)) := by sorry
