-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_UnfoldOrbit_bijective_mul_out_inv_b2a5c02b809d
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_UnfoldOrbit_bijective_mul_out_inv_b2a5c02b809d
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:39:04.882557+00:00
-- url     : https://prove2.me/theorems/06157f43-a097-54a2-9e58-5340b4bca9d2
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Unfold Orbit bijective mul out inv b2a5c02b809d: P2 M Ground Theory Heights  Heights Finite Covolume Unfold Orbit bijective mul out inv b2a5c02b809d
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Unfold Orbit bijective mul out inv b2a5c02b809d construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Unfold Orbit bijective mul out inv b2a5c02b809d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PUnfoldOrbit.lean#L11-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PUnfoldOrbit.lean#L11-L39

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_SecondCountableTopologyArchUnitary
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PUnfoldOrbit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open MeasureTheory
open scoped ENNReal Pointwise
variable (G : Type*) [Group G]

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_UnfoldOrbit_bijective_mul_out_inv_b2a5c02b809d {Γ Γ₀ : Subgroup G} (hle : Γ₀ ≤ Γ) :
    Function.Bijective (fun p : (Γ ⧸ Γ₀.subgroupOf Γ) × Γ₀ =>
      (⟨(p.2 : G) * ((Quotient.out p.1 : Γ) : G)⁻¹,
        Γ.mul_mem (hle p.2.2) (Γ.inv_mem (Quotient.out p.1).2)⟩ : Γ)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«UnfoldOrbit».«bijective_mul_out_inv» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_UnfoldOrbit_bijective_mul_out_inv_b2a5c02b809d
