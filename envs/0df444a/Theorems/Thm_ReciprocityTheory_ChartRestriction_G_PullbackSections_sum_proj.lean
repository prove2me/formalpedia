-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_sum_proj
-- name    : ReciprocityTheory.ChartRestriction.G.PullbackSections.sum_proj
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T10:33:29.008664+00:00
-- url     : https://prove2.me/theorems/ea6b3124-dd0a-4dfc-9cde-6d460121722d
-- title:
--   Pullback Sections: sum proj
-- statement:
--   The Pullback Sections construction uses the sum proj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/LieBridgeB.lean#L62-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/LieBridgeB.lean#L62-L67

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_LieBridgeB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections
open Polynomial
variable {K S M O ι : Type} [Field K] [CharZero K] [CommRing S] [Algebra K S] [AddCommGroup M] [Module S M]
  [CommRing O] [Fintype ι] [DecidableEq ι] (ρ : O →+* Module.End S M) (χ : ι → O →+* K) (α : O)

theorem ReciprocityTheory.ChartRestriction.G.PullbackSections.sum_proj [Nonempty ι] (hα : Function.Injective fun τ => χ τ α) : ∑ τ, proj ρ χ α τ = 1 := by sorry
