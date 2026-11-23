-- Prove2me | Theorems.Thm_P2M_UpperTheory_Reformulated_B_CyclicSubtraction_apply_eq_of_cycSub_eq_zero__fe379387d69c
-- name    : P2M_UpperTheory_Reformulated_B_CyclicSubtraction_apply_eq_of_cycSub_eq_zero__fe379387d69c
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:57:08.492111+00:00
-- url     : https://prove2.me/theorems/c8a1d731-b8cc-454b-88ff-483f8abccd0f
-- title:
--   P2 M Upper Theory Reformulated B Cyclic Subtraction apply eq of cyc Sub eq zero  fe379387d69c: P2 M Upper Theory Reformulated B Cyclic Subtraction apply eq of cyc Sub eq zero  fe379387d69c
-- statement:
--   The P2 M Upper Theory Reformulated B Cyclic Subtraction apply eq of cyc Sub eq zero  fe379387d69c construction uses the P2 M Upper Theory Reformulated B Cyclic Subtraction apply eq of cyc Sub eq zero  fe379387d69c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/CyclicSubtraction.lean#L8-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/CyclicSubtraction.lean#L8-L37

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CyclicSubtraction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem P2M_UpperTheory_Reformulated_B_CyclicSubtraction_apply_eq_of_cycSub_eq_zero__fe379387d69c.{u_1, u_2} :
    ∀ {G : Type u_1} {M : Type u_2} [inst : Group G] [inst_1 : AddCommGroup M] (ρ : Representation ℤ G M) {σ : G},
      (∀ (g : G), g ∈ Subgroup.zpowers σ) →
        ∀ {x : M}, (UpperTheory.Reformulated.B.CyclicSubtraction.cycSub ρ σ : M → M) x = (0 : M) → ∀ (g : G), ((ρ : G → M →ₗ[ℤ] M) g : M → M) x = x := by sorry

alias «UpperTheory».«Reformulated».«B».«CyclicSubtraction».«apply_eq_of_cycSub_eq_zero».«» := P2M_UpperTheory_Reformulated_B_CyclicSubtraction_apply_eq_of_cycSub_eq_zero__fe379387d69c
