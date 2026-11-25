-- Prove2me | Theorems.Thm_P2M_UpperTheory_Reformulated_B_NormLeOneOfMonicRoot_norm_le_one_of_monic_root__86b9da74710a
-- name    : P2M_UpperTheory_Reformulated_B_NormLeOneOfMonicRoot_norm_le_one_of_monic_root__86b9da74710a
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T13:44:19.428205+00:00
-- url     : https://prove2.me/theorems/d319adaf-a89a-4b08-a7fd-b7cd1cfb6bce
-- title:
--   P2 M Upper Theory Reformulated B Norm Le One Of Monic Root norm le one of monic root  86b9da74710a: P2 M Upper Theory Reformulated B Norm Le One Of Monic Root norm le one of monic root  86b9da74710a
-- statement:
--   The P2 M Upper Theory Reformulated B Norm Le One Of Monic Root norm le one of monic root  86b9da74710a construction uses the P2 M Upper Theory Reformulated B Norm Le One Of Monic Root norm le one of monic root  86b9da74710a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/NormLeOneOfMonicRoot.lean#L3-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/NormLeOneOfMonicRoot.lean#L3-L30

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_NormLeOneOfMonicRoot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem P2M_UpperTheory_Reformulated_B_NormLeOneOfMonicRoot_norm_le_one_of_monic_root__86b9da74710a.{u_1, u_2} :
    ∀ {R : Type u_1} {L : Type u_2} [inst : CommRing R] [inst_1 : NormedField L] [IsUltrametricDist L]
    (φ : R →+* L),
    (∀ (a : R), ‖(φ : R → L) a‖ ≤ (1 : ℝ)) →
      ∀ (x : L) (p : Polynomial R), p.Monic → Polynomial.eval₂ φ x p = (0 : L) → ‖x‖ ≤ (1 : ℝ) := by sorry

alias «UpperTheory».«Reformulated».«B».«NormLeOneOfMonicRoot».«norm_le_one_of_monic_root» := P2M_UpperTheory_Reformulated_B_NormLeOneOfMonicRoot_norm_le_one_of_monic_root__86b9da74710a
