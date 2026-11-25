-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_eig_of_alpha
-- name    : ReciprocityTheory.ChartRestriction.G.PullbackSections.eig_of_alpha
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:08:41.841502+00:00
-- url     : https://prove2.me/theorems/a1393d86-dbbc-4fd2-8d56-d51216c3c8bb
-- title:
--   Pullback Sections: eig of alpha
-- statement:
--   The Pullback Sections construction uses the eig of alpha property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/LieBridgeB.lean#L89-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/LieBridgeB.lean#L89-L108

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

theorem ReciprocityTheory.ChartRestriction.G.PullbackSections.eig_of_alpha (hN : ∀ a : O, ∃ (N : ℤ) (g : ℤ[X]), N ≠ 0 ∧ (N : O) * a = aeval α g) (τ : ι) {m : M}
    (hm : ρ α m = algebraMap K S (χ τ α) • m) : IsEigV ρ (χ τ) m := by sorry
