-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_card_piece_irrelevant_ideal
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.card_piece_irrelevant_ideal
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T14:11:02.792677+00:00
-- url     : https://prove2.me/theorems/048838de-42a7-5755-a321-9d1cba9b3150
-- title:
--   Arakelov Geometry: card piece irrelevant ideal
-- statement:
--   The Arakelov Geometry construction uses the card piece irrelevant ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/CardPieceIrrelevantIdeal.lean#L129-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/CardPieceIrrelevantIdeal.lean#L129-L155

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_EqSumMultihomogeneousComponents
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_CardPieceIrrelevantIdeal
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
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.card_piece_irrelevant_ideal {q : Ideal (MRing ι)} {k : K} (hk : ∀ i, (X ⟨k, i⟩ : MRing ι) ∈ q)
    {a : K → ℕ} (ha : 1 ≤ a k) : Nat.card (mPiece q a) = 1 := by sorry
