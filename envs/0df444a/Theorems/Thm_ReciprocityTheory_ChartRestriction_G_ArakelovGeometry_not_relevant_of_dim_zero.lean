-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_not_relevant_of_dim_zero
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.not_relevant_of_dim_zero
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T10:11:15.129971+00:00
-- url     : https://prove2.me/theorems/a8cdcf7d-12de-5d93-9704-7341a3b631e8
-- title:
--   Arakelov Geometry: not relevant of dim zero
-- statement:
--   The Arakelov Geometry construction uses the not relevant of dim zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/NotRelevantOfDimZero.lean#L133-L193
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/NotRelevantOfDimZero.lean#L133-L193

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_HasympAll
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_NotRelevantOfDimZero
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

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.not_relevant_of_dim_zero {W : Ideal (MRing ι)} [W.IsPrime] (hWm : IsMultiHomogIdeal W)
    (hd : ringKrullDim (MRing ι ⧸ W) = ((0 + Fintype.card K : ℕ) : WithBot ℕ∞))
    {s : MRing ι} {c : K → ℕ} (hs : IsMultiHomog s c) (hsW : s ∉ W) {W' : Ideal (MRing ι)}
    (hW' : W' ∈ (W ⊔ Ideal.span {s}).minimalPrimes) : ¬ IsRelevant W' := by sorry
