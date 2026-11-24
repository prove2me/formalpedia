-- Prove2me | Theorems.Thm_P2M_UpperTheory_Reformulated_B_FiniteTypeDescent_main__3dbb7f300c14
-- name    : P2M_UpperTheory_Reformulated_B_FiniteTypeDescent_main__3dbb7f300c14
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T11:11:47.308462+00:00
-- url     : https://prove2.me/theorems/20770910-aee8-41bc-b6c3-7e9b64a2042d
-- title:
--   P2 M Upper Theory Reformulated B Finite Type Descent main  3dbb7f300c14: P2 M Upper Theory Reformulated B Finite Type Descent main  3dbb7f300c14
-- statement:
--   The P2 M Upper Theory Reformulated B Finite Type Descent main  3dbb7f300c14 construction uses the P2 M Upper Theory Reformulated B Finite Type Descent main  3dbb7f300c14 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/ExistsRetr.lean#L38-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/ExistsRetr.lean#L38-L54

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ExistsRetr
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem P2M_UpperTheory_Reformulated_B_FiniteTypeDescent_main__3dbb7f300c14.{u_1, u_2, u_3} :
    ∀ (R : Type u_1) (C : Type u_2) (D : Type u_3) [inst : CommRing R] [inst_1 : CommRing C] [inst_2 : CommRing D]
      [inst_3 : Algebra R C] [inst_4 : Algebra C D] [inst_5 : Algebra R D] [IsScalarTower R C D] [Module.Finite C D]
      [Module.Projective C D],
      Function.Injective (⇑(Algebra.algebraMap C D) : C → D) → ∀ [Algebra.FiniteType R D], Algebra.FiniteType R C := by sorry

alias «UpperTheory».«Reformulated».«B».«FiniteTypeDescent».«main».«» := P2M_UpperTheory_Reformulated_B_FiniteTypeDescent_main__3dbb7f300c14
