-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_card_piece_of_filtration
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.card_piece_of_filtration
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T14:11:11.333785+00:00
-- url     : https://prove2.me/theorems/23d2daba-893f-5408-b894-72306fb215b5
-- title:
--   Arakelov Geometry: card piece of filtration
-- statement:
--   The Arakelov Geometry construction uses the card piece of filtration property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/CardPieceIrrelevantIdeal.lean#L100-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/CardPieceIrrelevantIdeal.lean#L100-L127

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

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.card_piece_of_filtration : ∀ (N : ℕ) (F : Fin (N + 1) → Ideal (MRing ι)) (f : Fin N → MRing ι)
    (c : Fin N → K → ℕ) (q : Fin N → Ideal (MRing ι)), IsMultiHomogIdeal (F 0) →
    F (Fin.last N) = ⊤ →
    (∀ j, IsMultiHomog (f j) (c j) ∧ F j.succ = F j.castSucc ⊔ Ideal.span {f j} ∧
      ∀ g, g ∈ q j ↔ g * f j ∈ F j.castSucc) →
    ∀ a : K → ℕ, (∀ j, c j ≤ a) →
      Nat.card (mPiece (F 0) a) = ∏ j, Nat.card (mPiece (q j) (a - c j))
  := by sorry
