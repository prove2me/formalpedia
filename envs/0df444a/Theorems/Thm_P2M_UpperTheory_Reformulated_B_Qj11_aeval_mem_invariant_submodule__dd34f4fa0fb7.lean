-- Prove2me | Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qj11_aeval_mem_invariant_submodule__dd34f4fa0fb7
-- name    : P2M_UpperTheory_Reformulated_B_Qj11_aeval_mem_invariant_submodule__dd34f4fa0fb7
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:21:22.866405+00:00
-- url     : https://prove2.me/theorems/9b5aa2cc-cdd6-51b0-ac7a-d6c44fb88f98
-- title:
--   P2 M Upper Theory Reformulated B Qj11 aeval mem invariant submodule  dd34f4fa0fb7: P2 M Upper Theory Reformulated B Qj11 aeval mem invariant submodule  dd34f4fa0fb7
-- statement:
--   The P2 M Upper Theory Reformulated B Qj11 aeval mem invariant submodule  dd34f4fa0fb7 construction uses the P2 M Upper Theory Reformulated B Qj11 aeval mem invariant submodule  dd34f4fa0fb7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/AevalMemInvariantSubmodule.lean#L3-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/AevalMemInvariantSubmodule.lean#L3-L19

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_AevalMemInvariantSubmodule
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem P2M_UpperTheory_Reformulated_B_Qj11_aeval_mem_invariant_submodule__dd34f4fa0fb7.{u_1} :
    ∀ {Y : Type u_1} [inst : AddCommGroup Y] [inst_1 : _root_.Module ℂ Y]
    (A : Module.End ℂ Y) (p : Submodule ℂ Y),
    (∀ y ∈ p, (A : Y → Y) y ∈ p) →
      ∀ (q : Polynomial ℂ), ∀ y ∈ p, ((Polynomial.aeval A : Polynomial ℂ → Module.End ℂ Y) q : Y → Y) y ∈ p := by sorry

alias «UpperTheory».«Reformulated».«B».«Qj11».«aeval_mem_invariant_submodule».«» := P2M_UpperTheory_Reformulated_B_Qj11_aeval_mem_invariant_submodule__dd34f4fa0fb7
