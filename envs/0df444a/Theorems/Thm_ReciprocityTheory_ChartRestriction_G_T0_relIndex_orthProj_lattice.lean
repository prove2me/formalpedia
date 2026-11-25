-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_relIndex_orthProj_lattice
-- name    : ReciprocityTheory.ChartRestriction.G.T0.relIndex_orthProj_lattice
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:40:26.032972+00:00
-- url     : https://prove2.me/theorems/ee18df1f-2ebc-41fa-90d9-bf06c98d5e92
-- title:
--   T0: rel Index orth Proj lattice
-- statement:
--   The T0 construction uses the rel Index orth Proj lattice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/ExistsSmallSaturatingVector.lean#L79-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/ExistsSmallSaturatingVector.lean#L79-L125

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_SingleMemStandardLattice
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ExistsNeZeroMemNormSqLeGramDetDivRelIndex
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_TheoremA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ExistsSmallSaturatingVector
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open Matrix NumberField
open scoped ComplexOrder
variable {K : Type} [Field K] [NumberField K] {r k : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.T0.relIndex_orthProj_lattice {m : ℕ} {b : Fin k → Fin r → K} (hb : LinearIndependent K b)
    (c : Fin m → Fin r → K) (hc : ∀ j, c j ∈ hStd K r) :
    (Submodule.span ℤ (Set.range (hwv b c))).toAddSubgroup.relIndex
        ((hStd K r).toAddSubgroup.map (hpvHom b)) =
      (ReciprocityTheory.MultiplicativeHeights.satSub (hStd K r) b ⊔ Submodule.span (𝓞 K) (Set.range c)).toAddSubgroup.relIndex
        (hStd K r).toAddSubgroup := by sorry
