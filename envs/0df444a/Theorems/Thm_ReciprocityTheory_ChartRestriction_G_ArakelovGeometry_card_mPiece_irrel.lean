-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_card_mPiece_irrel
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.card_mPiece_irrel
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:12:33.41626+00:00
-- url     : https://prove2.me/theorems/8ef2b80c-b538-420a-9748-a556cb1fb3f6
-- title:
--   Arakelov Geometry: card m Piece irrel
-- statement:
--   The Arakelov Geometry construction uses the card m Piece irrel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/SupportSubsetMonoBox.lean#L103-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/SupportSubsetMonoBox.lean#L103-L134

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsHomogeneousGrL
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_SupportSubsetMonoBox
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

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.card_mPiece_irrel {q : Ideal (MRing ι)} {k : K} (hk : ∀ i, (X ⟨k, i⟩ : MRing ι) ∈ q)
    {a : K → ℕ} (ha : 0 < a k) : Nat.card (mPiece q a) = 1 := by sorry
