-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagPull_eval__mul_blk_9a6df9c2595d
-- name    : P2M_GroundTheory_Heights__Heights_Inter_DiagPull_eval__mul_blk_9a6df9c2595d
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:30:57.945486+00:00
-- url     : https://prove2.me/theorems/3ffd6d89-1005-5f34-a5be-79fe2144b57a
-- title:
--   P2 M Ground Theory Heights  Heights Inter Diag Pull eval  mul blk 9a6df9c2595d: P2 M Ground Theory Heights  Heights Inter Diag Pull eval  mul blk 9a6df9c2595d
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Diag Pull eval  mul blk 9a6df9c2595d construction uses the P2 M Ground Theory Heights  Heights Inter Diag Pull eval  mul blk 9a6df9c2595d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagPull.lean#L70-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagPull.lean#L70-L84

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_MemDivSuppOfDivCycleNeZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedC
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PDiagPull
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.Inter.DiagPull
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Inter_DiagPull_eval__mul_blk_9a6df9c2595d {S : Type*} [CommRing S] {s : MRing ι} {d : K → ℕ} (hs : IsMultiHomog s d)
    (f : ℤ →+* S) (g : (Σ k, ι k) → S) (t : K → S) :
    eval₂ f (fun q => g q * t q.1) s = (∏ k, t k ^ d k) * eval₂ f g s := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«DiagPull».«eval₂_mul_blk» := P2M_GroundTheory_Heights__Heights_Inter_DiagPull_eval__mul_blk_9a6df9c2595d
