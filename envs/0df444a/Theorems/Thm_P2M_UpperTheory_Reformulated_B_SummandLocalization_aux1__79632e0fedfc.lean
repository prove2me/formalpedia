-- Prove2me | Theorems.Thm_P2M_UpperTheory_Reformulated_B_SummandLocalization_aux1__79632e0fedfc
-- name    : P2M_UpperTheory_Reformulated_B_SummandLocalization_aux1__79632e0fedfc
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T13:44:16.445469+00:00
-- url     : https://prove2.me/theorems/71cd6b69-feb9-4f02-abc0-44d51d37c716
-- title:
--   P2 M Upper Theory Reformulated B Summand Localization aux1  79632e0fedfc: P2 M Upper Theory Reformulated B Summand Localization aux1  79632e0fedfc
-- statement:
--   The P2 M Upper Theory Reformulated B Summand Localization aux1  79632e0fedfc construction uses the P2 M Upper Theory Reformulated B Summand Localization aux1  79632e0fedfc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/SummandLocalization.lean#L3-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/SummandLocalization.lean#L3-L10

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SummandLocalization
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem P2M_UpperTheory_Reformulated_B_SummandLocalization_aux1__79632e0fedfc.{u_1, u_2} :
    ∀ {R : Type u_2} [inst : CommRing R] {W : Type u_1} [inst_1 : AddCommGroup W] [inst_2 : _root_.Module R W]
      (S : Submonoid R) (L : Submodule R W) {x y : W},
      x ∈ {x : W | ∃ s ∈ S, s • x ∈ L} → y ∈ {x : W | ∃ s ∈ S, s • x ∈ L} → x + y ∈ {x : W | ∃ s ∈ S, s • x ∈ L} := by sorry

alias «UpperTheory».«Reformulated».«B».«SummandLocalization».«aux1».«» := P2M_UpperTheory_Reformulated_B_SummandLocalization_aux1__79632e0fedfc
