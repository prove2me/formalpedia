-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_two_le_krullDim_of_chain
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.two_le_krullDim_of_chain
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:10:16.655018+00:00
-- url     : https://prove2.me/theorems/b0313fc9-295d-51f7-ae3e-d815c9588d88
-- title:
--   Arakelov Geometry: two le krull Dim of chain
-- statement:
--   The Arakelov Geometry construction uses the two le krull Dim of chain property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/TwoLeKrullDimOfRelevantPrime.lean#L23-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/TwoLeKrullDimOfRelevantPrime.lean#L23-L38

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
variable {R : Type*} [CommRing R]

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.two_le_krullDim_of_chain (p₀ p₁ p₂ : Ideal R) [p₀.IsPrime]
    [p₁.IsPrime] [p₂.IsPrime] (h₀ : p₀ < p₁) (h₁ : p₁ < p₂) :
    ((2 : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ p₀) := by sorry
