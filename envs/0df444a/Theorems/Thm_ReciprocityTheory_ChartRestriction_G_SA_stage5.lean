-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_stage5
-- name    : ReciprocityTheory.ChartRestriction.G.SA.stage5
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:14:53.119935+00:00
-- url     : https://prove2.me/theorems/e757c6d6-11d7-4356-9a4d-11744f1b37f0
-- title:
--   SA: stage5
-- statement:
--   The SA construction uses the stage5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/StrongApproximation/HfDecompSelf.lean#L83-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/StrongApproximation/HfDecompSelf.lean#L83-L118

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_ReachableFixingAddSmulSecond
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_ExistsMaxOfNotCoprime
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_HfDecompSelf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.SA
open Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [CommRing K] {σ : K →+* K}
  {J : Matrix ι ι K}
variable (hσ : ∀ x, σ (σ x) = x) (hJ : Jᵀ = J.map σ) {e f : ι → K} (he : hf σ J e e = 0)
  (hff : hf σ J f f = 0) (hef : hf σ J e f = 1) {s : ℕ} {a : Fin s → ι → K}
  (hae : ∀ j, hf σ J (a j) e = 0) (haf : ∀ j, hf σ J (a j) f = 0)
  (hfix : ∀ x, σ x = x → x ≠ 0 → IsUnit x) {i2 : K} (h2i : 2 * i2 = 1) {δ : K} (hδ : IsUnit δ)
  (hσδ : σ δ = -δ) [IsReduced K]
include hσ hJ he hff hef hae haf hfix h2i hδ hσδ

theorem ReciprocityTheory.ChartRestriction.G.SA.stage5 {b : ι → K} (hform : b = hf σ J b f • e + hf σ J b e • f) (hα : IsUnit (hf σ J b f)) :
    Reach σ J e f a b (e + (hf σ J b b * i2) • f) := by sorry
