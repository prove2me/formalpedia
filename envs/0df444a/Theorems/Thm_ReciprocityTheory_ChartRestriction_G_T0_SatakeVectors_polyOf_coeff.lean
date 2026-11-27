-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_SatakeVectors_polyOf_coeff
-- name    : ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors.polyOf_coeff
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-27T05:46:34.376835+00:00
-- url     : https://prove2.me/theorems/0586efc1-f45e-4aa2-a9c9-0ce08b85198a
-- title:
--   Satake Vectors: poly Of coeff
-- statement:
--   The Satake Vectors construction uses the poly Of coeff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/ExistsIntMultiple.lean#L19-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/ExistsIntMultiple.lean#L19-L32

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

theorem ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors.polyOf_coeff {κ : Type} (S : Finset (κ →₀ ℕ)) (p : Fin S.card → K) (j : Fin S.card) :
    (polyOf S p).coeff (mS S j) = p j := by sorry
