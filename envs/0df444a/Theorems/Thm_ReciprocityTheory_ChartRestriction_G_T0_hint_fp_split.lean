-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_hint_fp_split
-- name    : ReciprocityTheory.ChartRestriction.G.T0.hint_fp_split
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-27T04:46:56.438713+00:00
-- url     : https://prove2.me/theorems/7ba435f4-7c80-4409-8d69-424eae864cd7
-- title:
--   T0: hint fp split
-- statement:
--   The T0 construction uses the hint fp split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/HintLogFinprod.lean#L18-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/HintLogFinprod.lean#L18-L41

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HtDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GoodPrimesProperties
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_NormFactorizationClause
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ComponentFormProperties
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HNormPts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_KTFiniteDimensional
import Definitions.Def_ReciprocityTheory_SemistableReduction_AevalIsWeightedHomogeneous
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HintIntOfBounds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HintLogFinprod
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField MeasureTheory ReciprocityTheory.MultiplicativeHeights

theorem ReciprocityTheory.ChartRestriction.G.T0.hint_fp_split {R Fr ι : Type*} [CommRing R] [Field Fr] [Algebra R Fr] (S : Set ι)
    (g : ι → R) (e : ι → ℤ) :
    ∃ s : Finset ι, (∀ p ∈ s, p ∈ S ∧ e p ≠ 0) ∧
      ∏ᶠ (p : ι) (_ : p ∈ S), algebraMap R Fr (g p) ^ e p =
        algebraMap R Fr (∏ p ∈ s, g p ^ (e p).toNat) /
          algebraMap R Fr (∏ p ∈ s, g p ^ (-e p).toNat) := by sorry
