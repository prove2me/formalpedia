-- Prove2me | Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qm12_vandermondeOf_eq_det__26efa66ef99e
-- name    : P2M_UpperTheory_Reformulated_B_Qm12_vandermondeOf_eq_det__26efa66ef99e
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:21:40.866964+00:00
-- url     : https://prove2.me/theorems/e221041d-4b61-4268-88de-35751fbbe973
-- title:
--   P2 M Upper Theory Reformulated B Qm12 vandermonde Of eq det  26efa66ef99e: P2 M Upper Theory Reformulated B Qm12 vandermonde Of eq det  26efa66ef99e
-- statement:
--   The P2 M Upper Theory Reformulated B Qm12 vandermonde Of eq det  26efa66ef99e construction uses the P2 M Upper Theory Reformulated B Qm12 vandermonde Of eq det  26efa66ef99e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/VandermondeOfEqDet.lean#L7-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/VandermondeOfEqDet.lean#L7-L23

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_VandermondeOfEqDet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem P2M_UpperTheory_Reformulated_B_Qm12_vandermondeOf_eq_det__26efa66ef99e.{u_1} :
    ∀ {m : ℕ} {R : Type u_1} [inst : CommRing R] (v : Fin m → R),
      UpperTheory.Reformulated.B.Qm12.vandermondeOf v =
        ((Matrix.of : (Fin m → Fin m → R) → Matrix (Fin m) (Fin m) R) fun (i j : Fin m) ↦
            v i ^ (m - (1 : ℕ) - (↑j : ℕ))).det := by sorry

alias «UpperTheory».«Reformulated».«B».«Qm12».«vandermondeOf_eq_det».«» := P2M_UpperTheory_Reformulated_B_Qm12_vandermondeOf_eq_det__26efa66ef99e
