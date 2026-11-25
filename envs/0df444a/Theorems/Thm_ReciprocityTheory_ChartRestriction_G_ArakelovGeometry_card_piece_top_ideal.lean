-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_card_piece_top_ideal
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.card_piece_top_ideal
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T10:03:20.800703+00:00
-- url     : https://prove2.me/theorems/106a43fb-8d9c-5ad3-9623-1b7e22735913
-- title:
--   Arakelov Geometry: card piece top ideal
-- statement:
--   The Arakelov Geometry construction uses the card piece top ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/CardPieceIrrelevantIdeal.lean#L96-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/CardPieceIrrelevantIdeal.lean#L96-L98

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

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.card_piece_top_ideal (a : K → ℕ) : Nat.card (mPiece (⊤ : Ideal (MRing ι)) a) = 1 := by sorry
