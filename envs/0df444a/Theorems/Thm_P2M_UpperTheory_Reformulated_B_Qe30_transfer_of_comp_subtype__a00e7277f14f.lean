-- Prove2me | Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qe30_transfer_of_comp_subtype__a00e7277f14f
-- name    : P2M_UpperTheory_Reformulated_B_Qe30_transfer_of_comp_subtype__a00e7277f14f
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T13:43:48.787242+00:00
-- url     : https://prove2.me/theorems/53fa7da0-3cd1-5b2e-9b42-6fd808bc071a
-- title:
--   P2 M Upper Theory Reformulated B Qe30 transfer of comp subtype  a00e7277f14f: P2 M Upper Theory Reformulated B Qe30 transfer of comp subtype  a00e7277f14f
-- statement:
--   The P2 M Upper Theory Reformulated B Qe30 transfer of comp subtype  a00e7277f14f construction uses the P2 M Upper Theory Reformulated B Qe30 transfer of comp subtype  a00e7277f14f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/TransferOfCompSubtype.lean#L3-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/TransferOfCompSubtype.lean#L3-L15

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_TransferOfCompSubtype
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem P2M_UpperTheory_Reformulated_B_Qe30_transfer_of_comp_subtype__a00e7277f14f.{u_1} :
    ∀ {Γ : Type u_1} [inst : Group Γ] (H : Subgroup Γ)
    [inst_1 : H.FiniteIndex] (g : Γ),
    ((Abelianization.of.comp H.subtype).transfer : Γ → Abelianization Γ) g =
      (Abelianization.of : Γ → Abelianization Γ) g ^ H.index := by sorry

alias «UpperTheory».«Reformulated».«B».«Qe30».«transfer_of_comp_subtype».«» := P2M_UpperTheory_Reformulated_B_Qe30_transfer_of_comp_subtype__a00e7277f14f
