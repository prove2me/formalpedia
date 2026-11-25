-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_orthProj_mem_span
-- name    : ReciprocityTheory.ChartRestriction.G.T0.orthProj_mem_span
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T10:39:44.255299+00:00
-- url     : https://prove2.me/theorems/7623ba01-aef7-4955-b78c-67e5a0bd8af3
-- title:
--   T0: orth Proj mem span
-- statement:
--   The T0 construction uses the orth Proj mem span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/ExistsSmallSaturatingVector.lean#L51-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/ExistsSmallSaturatingVector.lean#L51-L69

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

theorem ReciprocityTheory.ChartRestriction.G.T0.orthProj_mem_span {m : ℕ} (b : Fin k → Fin r → K) (c : Fin m → Fin r → K) {t : Fin r → K}
    (ht : t ∈ Submodule.span (𝓞 K) (Set.range c)) :
    hpv b t ∈ Submodule.span ℤ (Set.range (hwv b c)) := by sorry
