-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_exists_int_mul_mem_of_mem_qIdeal
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.exists_int_mul_mem_of_mem_qIdeal
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:14:21.584835+00:00
-- url     : https://prove2.me/theorems/99481db4-761a-4424-8eee-4318633d9d72
-- title:
--   Geo: exists int mul mem of mem q Ideal
-- statement:
--   The Geo construction uses the exists int mul mem of mem q Ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterGoodB.lean#L35-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterGoodB.lean#L35-L59

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGoodA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGoodB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
open MvPolynomial
noncomputable section
variable {σ : Type}

theorem ReciprocityTheory.ChartRestriction.G.Geo.exists_int_mul_mem_of_mem_qIdeal (P : Ideal (MvPolynomial σ ℤ)) {g : MvPolynomial σ ℚ}
    (hg : g ∈ qIdeal P) :
    ∃ N : ℤ, N ≠ 0 ∧ ∃ h ∈ P, (N : MvPolynomial σ ℚ) * g = qmap h := by sorry
