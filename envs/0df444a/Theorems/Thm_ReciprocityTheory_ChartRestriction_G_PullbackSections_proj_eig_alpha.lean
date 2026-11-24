-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_proj_eig_alpha
-- name    : ReciprocityTheory.ChartRestriction.G.PullbackSections.proj_eig_alpha
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:14:39.440088+00:00
-- url     : https://prove2.me/theorems/8da4645c-46dc-4a22-a9e1-40659eb414b8
-- title:
--   Pullback Sections: proj eig alpha
-- statement:
--   The Pullback Sections construction uses the proj eig alpha property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/LieBridgeB.lean#L69-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/LieBridgeB.lean#L69-L87

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

theorem ReciprocityTheory.ChartRestriction.G.PullbackSections.proj_eig_alpha (hα : Function.Injective fun τ => χ τ α) (f : ℤ[X]) (hf : aeval α f = 0)
    (hfs : f.map (Int.castRingHom K) = ∏ τ, (X - C (χ τ α))) (τ : ι) (m : M) :
    ρ α (proj ρ χ α τ m) = algebraMap K S (χ τ α) • proj ρ χ α τ m := by sorry
