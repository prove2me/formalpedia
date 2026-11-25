-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_ComponentData_n_eq_ff3eec8b4d03
-- name    : P2M_GroundTheory_Heights__Heights_LowerBoundFree_ComponentData_n_eq_ff3eec8b4d03
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T13:29:42.727643+00:00
-- url     : https://prove2.me/theorems/c554716a-6601-4628-a902-c5739284e785
-- title:
--   P2 M Ground Theory Heights  Heights Lower Bound Free Component Data n eq ff3eec8b4d03: P2 M Ground Theory Heights  Heights Lower Bound Free Component Data n eq ff3eec8b4d03
-- statement:
--   The P2 M Ground Theory Heights  Heights Lower Bound Free Component Data n eq ff3eec8b4d03 construction uses the P2 M Ground Theory Heights  Heights Lower Bound Free Component Data n eq ff3eec8b4d03 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/CoordinateIdeals.lean#L239-L239
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/CoordinateIdeals.lean#L239-L239

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_Bundle
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ArithmeticHilbertSamuelLowerBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_CoordinateIdeals
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
open scoped Matrix ComplexOrder
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
open GroundTheory.Heights₂.Heights.LowerBoundFree.ComponentData
variable {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] {Ω : Type} [Field Ω] [Algebra ℚ Ω]
  {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)]
  (D : ComponentData II Ψ K ι Ω E)

theorem P2M_GroundTheory_Heights__Heights_LowerBoundFree_ComponentData_n_eq_ff3eec8b4d03 : D.n = D.f * D.j * D.j' := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LowerBoundFree».«ComponentData».«n_eq» := P2M_GroundTheory_Heights__Heights_LowerBoundFree_ComponentData_n_eq_ff3eec8b4d03
