-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_card_mPiece_chain
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.card_mPiece_chain
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T10:03:40.395037+00:00
-- url     : https://prove2.me/theorems/fd682f96-4a58-5431-9398-22a77987d8fc
-- title:
--   Arakelov Geometry: card m Piece chain
-- statement:
--   The Arakelov Geometry construction uses the card m Piece chain property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/IsMultiHomogIdealChain.lean#L79-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/IsMultiHomogIdealChain.lean#L79-L101

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AbsProdSubProdSubLinLe
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_LengthLocQuotEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsMultiHomogIdealChain
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

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.card_mPiece_chain (a : K → ℕ) : ∀ (N : ℕ) (F : Fin (N + 1) → Ideal (MRing ι))
    (f : Fin N → MRing ι) (c : Fin N → K → ℕ) (q : Fin N → Ideal (MRing ι)),
    IsMultiHomogIdeal (F 0) → F (Fin.last N) = ⊤ →
    (∀ j : Fin N, IsMultiHomog (f j) (c j) ∧ F j.succ = F j.castSucc ⊔ Ideal.span {f j} ∧
      ∀ g, g ∈ q j ↔ g * f j ∈ F j.castSucc) →
    (∀ j k, c j k ≤ a k) →
    Nat.card (mPiece (F 0) a) = ∏ j, Nat.card (mPiece (q j) (a - c j))
  := by sorry
