-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Pdiv_FiniteLocalHoms_exists_lift_nil
-- name    : ReciprocityTheory.ChartRestriction.G.Pdiv.FiniteLocalHoms.exists_lift_nil
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T10:32:04.874406+00:00
-- url     : https://prove2.me/theorems/ff43adbd-9f75-4083-af84-730bcab20385
-- title:
--   Finite Local Homs: exists lift nil
-- statement:
--   The Finite Local Homs construction uses the exists lift nil property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PlaceDivisors/FiniteLocalLifts/SmLift.lean#L11-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PlaceDivisors/FiniteLocalLifts/SmLift.lean#L11-L77

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_FiniteLocalLifts_SmLift
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Pdiv.FiniteLocalHoms
variable {R : Type} [CommRing R] {A W K : Type} [CommRing A] [CommRing W] [CommRing K]
  [Algebra R A] [Algebra R W] [Algebra R K]

theorem ReciprocityTheory.ChartRestriction.G.Pdiv.FiniteLocalHoms.exists_lift_nil [Algebra.FormallySmooth R A] [Algebra.FinitePresentation R A]
    (ρ : W →ₐ[R] K) (hsurj : Function.Surjective ρ) (hnil : ∀ a ∈ RingHom.ker ρ, IsNilpotent a)
    (φ : A →ₐ[R] K) : ∃ ψ : A →ₐ[R] W, ρ.comp ψ = φ := by sorry
