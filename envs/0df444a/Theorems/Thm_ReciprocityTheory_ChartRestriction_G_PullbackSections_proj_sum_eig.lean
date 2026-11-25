-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_proj_sum_eig
-- name    : ReciprocityTheory.ChartRestriction.G.PullbackSections.proj_sum_eig
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:25:51.938808+00:00
-- url     : https://prove2.me/theorems/fee30438-61ad-48e8-954c-0feabb738570
-- title:
--   Pullback Sections: proj sum eig
-- statement:
--   The Pullback Sections construction uses the proj sum eig property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/LieBridgeB.lean#L110-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/LieBridgeB.lean#L110-L120

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

theorem ReciprocityTheory.ChartRestriction.G.PullbackSections.proj_sum_eig (hα : Function.Injective fun τ => χ τ α) (mm : ι → M)
    (hmm : ∀ τ, IsEigV ρ (χ τ) (mm τ)) (τ : ι) : proj ρ χ α τ (∑ τ', mm τ') = mm τ := by sorry
