-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_card_mPiece_eq
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.card_mPiece_eq
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T10:03:42.4058+00:00
-- url     : https://prove2.me/theorems/c07813ae-c176-5ad1-a3b4-ce41d145b494
-- title:
--   Arakelov Geometry: card m Piece eq
-- statement:
--   The Arakelov Geometry construction uses the card m Piece eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/IsHomogeneousGrL.lean#L57-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/IsHomogeneousGrL.lean#L57-L60

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ExistsPrimeFiltrationOfIsMultiHomogIdeal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsHomogeneousGrL
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
attribute [local instance 2000] lexDecEq
attribute [local instance] MvPolynomial.weightedGradedAlgebra
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.card_mPiece_eq (J : Ideal (MRing ι)) (a : K → ℕ) :
    Nat.card (mPiece J a) = Nat.card (mHom ι a ⧸ LinearMap.ker (pieceMap J a)) := by sorry
