-- Prove2me | Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qm9_det_sq_eq_one_of_preserves_bilin__0c529749593d
-- name    : P2M_UpperTheory_Reformulated_B_Qm9_det_sq_eq_one_of_preserves_bilin__0c529749593d
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:21:42.468103+00:00
-- url     : https://prove2.me/theorems/3db1b08d-2d08-55ef-bb26-324ee0f368a9
-- title:
--   P2 M Upper Theory Reformulated B Qm9 det sq eq one of preserves bilin  0c529749593d: P2 M Upper Theory Reformulated B Qm9 det sq eq one of preserves bilin  0c529749593d
-- statement:
--   The P2 M Upper Theory Reformulated B Qm9 det sq eq one of preserves bilin  0c529749593d construction uses the P2 M Upper Theory Reformulated B Qm9 det sq eq one of preserves bilin  0c529749593d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/DetSqEqOneOfPreservesBilin.lean#L3-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/DetSqEqOneOfPreservesBilin.lean#L3-L23

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_DetSqEqOneOfPreservesBilin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem P2M_UpperTheory_Reformulated_B_Qm9_det_sq_eq_one_of_preserves_bilin__0c529749593d.{u_1} :
    ∀ {V : Type u_1} [inst : AddCommGroup V]
    [inst_1 : _root_.Module ℝ V] [FiniteDimensional ℝ V] (B : LinearMap.BilinForm ℝ V),
    B.Nondegenerate →
      ∀ (f : V →ₗ[ℝ] V),
        (∀ (x y : V), ((B : V → V →ₗ[ℝ] ℝ) ((f : V → V) x) : V → ℝ) ((f : V → V) y) = ((B : V → V →ₗ[ℝ] ℝ) x : V → ℝ) y) →
          (LinearMap.det : (V →ₗ[ℝ] V) → ℝ) f ^ (2 : ℕ) = (1 : ℝ) := by sorry

alias «UpperTheory».«Reformulated».«B».«Qm9».«det_sq_eq_one_of_preserves_bilin».«» := P2M_UpperTheory_Reformulated_B_Qm9_det_sq_eq_one_of_preserves_bilin__0c529749593d
