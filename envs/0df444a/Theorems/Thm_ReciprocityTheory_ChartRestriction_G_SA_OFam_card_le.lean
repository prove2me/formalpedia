-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_OFam_card_le
-- name    : ReciprocityTheory.ChartRestriction.G.SA.OFam.card_le
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:19:08.53289+00:00
-- url     : https://prove2.me/theorems/483ead72-ad35-4782-b53a-f0c3cd935a5f
-- title:
--   OFam: card le
-- statement:
--   The OFam construction uses the card le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/StrongApproximation/SubProjOrth.lean#L265-L332
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/StrongApproximation/SubProjOrth.lean#L265-L332

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_EichAlongSub
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_SubProjOrth
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
variable {e f : ι → K}
variable (hσ : ∀ x, σ (σ x) = x) (hJ : Jᵀ = J.map σ) (he : hf σ J e e = 0) (hff : hf σ J f f = 0)
  (hef : hf σ J e f = 1) (hdet : IsUnit J.det) (hfix : ∀ x, σ x = x → x ≠ 0 → IsUnit x)
  (h2 : IsUnit (2 : K)) {δ : K} (hδ : IsUnit δ) (hσδ : σ δ = -δ)
include hσ hJ he hff hef

theorem ReciprocityTheory.ChartRestriction.G.SA.OFam.card_le [Nontrivial K] {r : ℕ} (F : OFam σ J e f r) : r + 2 ≤ Fintype.card ι := by sorry
