-- Prove2me | Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qn10_sum_r_mul_ne__f17edb41f5d8
-- name    : P2M_UpperTheory_Reformulated_B_Qn10_sum_r_mul_ne__f17edb41f5d8
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T11:27:04.211842+00:00
-- url     : https://prove2.me/theorems/0a41c6f4-d942-4844-9eef-2c90b500be26
-- title:
--   P2 M Upper Theory Reformulated B Qn10 sum r mul ne  f17edb41f5d8: P2 M Upper Theory Reformulated B Qn10 sum r mul ne  f17edb41f5d8
-- statement:
--   The P2 M Upper Theory Reformulated B Qn10 sum r mul ne  f17edb41f5d8 construction uses the P2 M Upper Theory Reformulated B Qn10 sum r mul ne  f17edb41f5d8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/SumRMulNe.lean#L3-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/SumRMulNe.lean#L3-L22

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SumRMulNe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem P2M_UpperTheory_Reformulated_B_Qn10_sum_r_mul_ne__f17edb41f5d8.{u_1} :
    ∀ {A : Type u_1} [inst : CommRing A] [IsDomain A]
    {n : ℕ} (f : MvPolynomial (Fin (n + (1 : ℕ))) A) (v w : Fin (n + (1 : ℕ)) →₀ ℕ),
    (∀ (i : Fin (n + (1 : ℕ))), (v : Fin (n + (1 : ℕ)) → ℕ) i < (2 : ℕ) + f.totalDegree) →
      (∀ (i : Fin (n + (1 : ℕ))), (w : Fin (n + (1 : ℕ)) → ℕ) i < (2 : ℕ) + f.totalDegree) →
        v ≠ w →
          ∑ x : Fin (n + (1 : ℕ)),
              (fun (i : Fin (n + (1 : ℕ))) ↦ ((2 : ℕ) + f.totalDegree) ^ (↑i : ℕ)) x * (v : Fin (n + (1 : ℕ)) → ℕ) x ≠
            ∑ x : Fin (n + (1 : ℕ)),
              (fun (i : Fin (n + (1 : ℕ))) ↦ ((2 : ℕ) + f.totalDegree) ^ (↑i : ℕ)) x * (w : Fin (n + (1 : ℕ)) → ℕ) x := by sorry

alias «UpperTheory».«Reformulated».«B».«Qn10».«sum_r_mul_ne».«» := P2M_UpperTheory_Reformulated_B_Qn10_sum_r_mul_ne__f17edb41f5d8
