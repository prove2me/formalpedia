-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_SatakeVectors_support_polyOf
-- name    : ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors.support_polyOf
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-27T05:47:21.511027+00:00
-- url     : https://prove2.me/theorems/07d6ddcf-84bc-4fa2-b7e9-bab7df687c78
-- title:
--   Satake Vectors: support poly Of
-- statement:
--   The Satake Vectors construction uses the support poly Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/ExistsIntMultiple.lean#L54-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/ExistsIntMultiple.lean#L54-L66

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

theorem ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors.support_polyOf {κ : Type} [DecidableEq κ] (G : MvPolynomial κ K) (S T : Finset (κ →₀ ℕ))
    (hST : ∀ m ∈ S, (G * MvPolynomial.monomial m 1).support ⊆ T) (p : Fin S.card → K) :
    (G * polyOf S p).support ⊆ T := by sorry
