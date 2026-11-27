-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_two_le_krullDim_of_relevant_prime
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.two_le_krullDim_of_relevant_prime
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T14:12:16.088584+00:00
-- url     : https://prove2.me/theorems/e17d6adc-6432-4138-85bc-a8dae2440466
-- title:
--   Arakelov Geometry: two le krull Dim of relevant prime
-- statement:
--   The Arakelov Geometry construction uses the two le krull Dim of relevant prime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/TwoLeKrullDimOfRelevantPrime.lean#L128-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/TwoLeKrullDimOfRelevantPrime.lean#L128-L149

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_CardPieceIrrelevantIdeal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LengthCokerEqKerAddDimOneOrderSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_TwoLeKrullDimOfRelevantPrime
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

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.two_le_krullDim_of_relevant_prime {ι : Fin 2 → Type} [∀ k, Fintype (ι k)] {q : Ideal (MRing ι)}
    (hq : IsMultiProjPrime q) : ((2 : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (MRing ι ⧸ q) := by sorry
