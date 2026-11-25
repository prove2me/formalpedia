-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_card_piece_colon_exact
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.card_piece_colon_exact
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T10:04:28.050332+00:00
-- url     : https://prove2.me/theorems/8deca70f-96bd-4a0b-b4e4-eccb03b7a7fd
-- title:
--   Arakelov Geometry: card piece colon exact
-- statement:
--   The Arakelov Geometry construction uses the card piece colon exact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/CardPieceIrrelevantIdeal.lean#L28-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/CardPieceIrrelevantIdeal.lean#L28-L94

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

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.card_piece_colon_exact {F q : Ideal (MRing ι)} (hF : IsMultiHomogIdeal F) {f : MRing ι} {c : K → ℕ}
    (hf : IsMultiHomog f c) (hq : ∀ g, g ∈ q ↔ g * f ∈ F) {a : K → ℕ} (hca : c ≤ a) :
    Nat.card (mPiece F a) =
      Nat.card (mPiece q (a - c)) * Nat.card (mPiece (F ⊔ Ideal.span {f}) a) := by sorry
