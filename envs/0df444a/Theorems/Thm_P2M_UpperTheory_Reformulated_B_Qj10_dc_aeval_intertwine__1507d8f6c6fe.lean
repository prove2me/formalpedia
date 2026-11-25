-- Prove2me | Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qj10_dc_aeval_intertwine__1507d8f6c6fe
-- name    : P2M_UpperTheory_Reformulated_B_Qj10_dc_aeval_intertwine__1507d8f6c6fe
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:21:22.887121+00:00
-- url     : https://prove2.me/theorems/ee6c7bd4-a3a0-5da8-a3c5-22cdde932d40
-- title:
--   P2 M Upper Theory Reformulated B Qj10 dc aeval intertwine  1507d8f6c6fe: P2 M Upper Theory Reformulated B Qj10 dc aeval intertwine  1507d8f6c6fe
-- statement:
--   The P2 M Upper Theory Reformulated B Qj10 dc aeval intertwine  1507d8f6c6fe construction uses the P2 M Upper Theory Reformulated B Qj10 dc aeval intertwine  1507d8f6c6fe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/DcAevalIntertwine.lean#L3-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/DcAevalIntertwine.lean#L3-L22

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_DcAevalIntertwine
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem P2M_UpperTheory_Reformulated_B_Qj10_dc_aeval_intertwine__1507d8f6c6fe.{u_1, u_2} :
    ∀ {Y : Type u_1} {Z : Type u_2} [inst : AddCommGroup Y] [inst_1 : _root_.Module ℂ Y] [inst_2 : AddCommGroup Z]
    [inst_3 : _root_.Module ℂ Z] (ψ : Y →ₗ[ℂ] Z) (A : Module.End ℂ Y) (B : Module.End ℂ Z),
    (∀ (y : Y), (ψ : Y → Z) ((A : Y → Y) y) = (B : Z → Z) ((ψ : Y → Z) y)) →
      ∀ (p : Polynomial ℂ) (y : Y),
        (ψ : Y → Z) (((Polynomial.aeval A : Polynomial ℂ → Module.End ℂ Y) p : Y → Y) y) =
          ((Polynomial.aeval B : Polynomial ℂ → Module.End ℂ Z) p : Z → Z) ((ψ : Y → Z) y) := by sorry

alias «UpperTheory».«Reformulated».«B».«Qj10».«dc_aeval_intertwine».«» := P2M_UpperTheory_Reformulated_B_Qj10_dc_aeval_intertwine__1507d8f6c6fe
