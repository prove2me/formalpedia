-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_NPB_exists_gen
-- name    : ReciprocityTheory.ChartRestriction.G.T0.NPB.exists_gen
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:02:55.253796+00:00
-- url     : https://prove2.me/theorems/2007d467-f3d3-43a0-96aa-a9ddf36be092
-- title:
--   NPB: exists gen
-- statement:
--   The NPB construction uses the exists gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/CastAddNeNatAdd.lean#L194-L211
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/CastAddNeNatAdd.lean#L194-L211

import Definitions.Def_ReciprocityTheory_SemistableReduction_AeBlockSphereEvalNeZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_CastAddNeNatAdd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0 ReciprocityTheory.ChartRestriction.G.T0.NPB
open MvPolynomial MeasureTheory ReciprocityTheory.MultiplicativeHeights
variable {K : Type} [Field K] {D N : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.T0.NPB.exists_gen (sg : K →+* ℂ) [Countable K] (tt : Fin D × Fin (N + 1) → ℂ)
    (hG : ∀ (a : Fin D → ℕ) (p : MvPolynomial (Fin D × Fin (N + 1)) K),
      IsMultiHomogeneous a p → p ≠ 0 → eval₂ sg tt p ≠ 0)
    (Q : MvPolynomial (Fin (N + 1 + D)) ℂ) (hQ : Q ≠ 0) :
    ∃ y : Fin (N + 1 + D) → ℂ, eval y Q ≠ 0 ∧
      ∀ q : MvPolynomial (Fin (D + 1) × Fin (N + 1)) K, q ≠ 0 → eval₂ sg (gpt tt y) q ≠ 0 := by sorry
