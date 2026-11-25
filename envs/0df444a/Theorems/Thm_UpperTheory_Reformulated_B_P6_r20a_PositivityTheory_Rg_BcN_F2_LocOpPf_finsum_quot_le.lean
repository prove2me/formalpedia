-- Prove2me | Theorems.Thm_UpperTheory_Reformulated_B_P6_r20a_PositivityTheory_Rg_BcN_F2_LocOpPf_finsum_quot_le
-- name    : UpperTheory.Reformulated.B.P6.r20a.PositivityTheory.Rg.BcN.F2.LocOpPf.finsum_quot_le
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T16:46:50.404133+00:00
-- url     : https://prove2.me/theorems/ad77d6d1-2124-4762-990d-979e181b2dec
-- title:
--   Loc Op Pf: finsum quot le
-- statement:
--   The Loc Op Pf construction uses the finsum quot le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/SchwartzBilinear/QuotientOutRightInvariant.lean#L16-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/SchwartzBilinear/QuotientOutRightInvariant.lean#L16-L63

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SchwartzBilinear_QuotientOutRightInvariant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UpperTheory UpperTheory.Reformulated UpperTheory.Reformulated.B UpperTheory.Reformulated.B.P6 UpperTheory.Reformulated.B.P6.r20a

theorem UpperTheory.Reformulated.B.P6.r20a.PositivityTheory.Rg.BcN.F2.LocOpPf.finsum_quot_le :
    ∀ {H : Type} [inst : Group H] {S T : Subgroup H}, S ≤ T → ∀ (u : H → ℂ), (∀ (x t : H), t ∈ T → u (x * t) = u x) → S.relIndex T ≠ OfNat.ofNat (nat_lit 0) → (Function.support fun (q : H ⧸ S) ↦ u (Quotient.out q)).Finite → ∑ᶠ (q : H ⧸ S), u (Quotient.out q) = (S.relIndex T).cast * ∑ᶠ (q : H ⧸ T), u (Quotient.out q) := by sorry
