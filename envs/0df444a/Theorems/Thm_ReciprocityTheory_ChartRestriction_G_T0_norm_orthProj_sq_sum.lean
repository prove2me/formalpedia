-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_norm_orthProj_sq_sum
-- name    : ReciprocityTheory.ChartRestriction.G.T0.norm_orthProj_sq_sum
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T10:40:39.130594+00:00
-- url     : https://prove2.me/theorems/b97ed0ad-ba4d-444a-a1c0-9ad91a3b2078
-- title:
--   T0: norm orth Proj sq sum
-- statement:
--   The T0 construction uses the norm orth Proj sq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/ExistsSmallSaturatingVector.lean#L45-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/ExistsSmallSaturatingVector.lean#L45-L49

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

theorem ReciprocityTheory.ChartRestriction.G.T0.norm_orthProj_sq_sum {b : Fin k → Fin r → K} (hb : LinearIndependent K b) (q : Fin r → K) :
    ‖hpv b q‖ ^ 2 = ∑ σ, hQdist σ b q ^ 2 := by sorry
