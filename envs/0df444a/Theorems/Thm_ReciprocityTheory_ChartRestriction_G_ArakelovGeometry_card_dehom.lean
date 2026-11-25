-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_card_dehom
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.card_dehom
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T10:07:17.715335+00:00
-- url     : https://prove2.me/theorems/70061a8e-db88-5d5a-b6a8-f24c6d85ecfc
-- title:
--   Arakelov Geometry: card dehom
-- statement:
--   The Arakelov Geometry construction uses the card dehom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/NatCardEqPowLength.lean#L117-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/NatCardEqPowLength.lean#L117-L148

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsMultiHomogXpow
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_NatCardEqPowLength
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
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.card_dehom {W : Ideal (MRing ι)} (hWp : W.IsPrime) (hWm : IsMultiHomogIdeal W)
    {i : ∀ k, ι k} (hi : ∀ k, (X ⟨k, i k⟩ : MRing ι) ∉ W) {a₁ c0 : ℕ}
    (hconst : ∀ a : K → ℕ, (∀ k, a₁ ≤ a k) → Nat.card (mPiece W a) = c0)
    (hfin : ∀ a : K → ℕ, Finite (mPiece W a)) {a : K → ℕ} (ha : ∀ k, a₁ ≤ a k) :
    Nat.card (MRing ι ⧸ dehomI W i) = c0 := by sorry
