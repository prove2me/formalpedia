-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_gtD_lat
-- name    : ReciprocityTheory.ChartRestriction.G.T0.gtD_lat
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T10:37:44.699872+00:00
-- url     : https://prove2.me/theorems/7f9a706a-47a9-52da-b505-b54df229f4e1
-- title:
--   T0: gt D lat
-- statement:
--   The T0 construction uses the gt D lat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/TransferenceB.lean#L63-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/TransferenceB.lean#L63-L131

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_TransferenceB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open Module Submodule

theorem ReciprocityTheory.ChartRestriction.G.T0.gtD_lat {m : ℕ} (b : Basis (Fin (m + 1)) ℝ (EuclideanSpace ℝ (Fin (m + 1))))
    (y0 xu : EuclideanSpace ℝ (Fin (m + 1))) (hy0 : y0 ≠ 0) (hxu : xu ∈ span ℤ (Set.range b))
    (h1 : inner ℝ y0 xu = 1) (hint : ∀ j, ∃ k : ℤ, inner ℝ y0 (b j) = k) :
    ∃ bW : Basis (Fin m) ℝ (ℝ ∙ y0)ᗮ,
      (∀ x ∈ span ℤ (Set.range bW),
        ((x : (ℝ ∙ y0)ᗮ) : EuclideanSpace ℝ (Fin (m + 1))) ∈ span ℤ (Set.range b)) ∧
      (∀ v ∈ span ℤ (Set.range b), ∃ p ∈ span ℤ (Set.range bW),
        (p : EuclideanSpace ℝ (Fin (m + 1))) = v - inner ℝ y0 v • xu) := by sorry
