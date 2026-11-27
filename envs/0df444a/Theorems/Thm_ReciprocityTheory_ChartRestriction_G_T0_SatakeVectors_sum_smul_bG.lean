-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_SatakeVectors_sum_smul_bG
-- name    : ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors.sum_smul_bG
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-27T05:47:33.31615+00:00
-- url     : https://prove2.me/theorems/b1acb553-7817-4fc1-8831-dbffc08e6426
-- title:
--   Satake Vectors: sum smul b G
-- statement:
--   The Satake Vectors construction uses the sum smul b G property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/ExistsIntMultiple.lean#L42-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/ExistsIntMultiple.lean#L42-L52

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GaussAbsMulSupportFinite
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ExistsIntMultiple
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0 ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors
open NumberField IsDedekindDomain
variable {K : Type} [Field K] [NumberField K]

theorem ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors.sum_smul_bG {κ : Type} (G : MvPolynomial κ K) (S : Finset (κ →₀ ℕ)) {T : Finset (κ →₀ ℕ)}
    {r : ℕ} (e : T ≃ Fin r) (p : Fin S.card → K) :
    ∑ j, p j • bG G S e j = coordVec e (G * polyOf S p) := by sorry
