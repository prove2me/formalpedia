-- Prove2me | Theorems.Thm_UpperTheory_Reformulated_B_P6_r26a_commutator_casimir_term
-- name    : UpperTheory.Reformulated.B.P6.r26a.commutator_casimir_term
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:12:35.131689+00:00
-- url     : https://prove2.me/theorems/da21d7e3-087d-4e54-bafc-3406b462273f
-- title:
--   r26a: commutator casimir term
-- statement:
--   The r26a construction uses the commutator casimir term property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/SchwartzBilinear/DoubleSumReduceSecond.lean#L15-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/SchwartzBilinear/DoubleSumReduceSecond.lean#L15-L36

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SchwartzBilinear_DoubleSumReduceSecond
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UpperTheory UpperTheory.Reformulated UpperTheory.Reformulated.B UpperTheory.Reformulated.B.P6 UpperTheory.Reformulated.B.P6.r26a
open scoped HSub SubNegMonoid AddGroup AddGroupWithOne Ring HMul Distrib OfNat Zero MulZeroClass Finset Semiring Fin Complex AddCommGroup Module Module.End

theorem UpperTheory.Reformulated.B.P6.r26a.commutator_casimir_term {V : Type} [AddCommGroup V] [_root_.Module ℂ V] {n : ℕ} (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) (hK : PositivityTheory.D.DSIC.KRel ε E) {c d : Fin n} (hcd : ε c = ε d)
    (a b : Fin n) :
    E c d * (if ε a = ε b then E a b * E b a else 0) - (if ε a = ε b then E a b * E b a else 0) * E c d
      = ((if ε a = ε b then (if d = a then E c b * E b a else 0) else 0)
          - (if ε a = ε b then (if a = c then E a b * E b d else 0) else 0))
        + ((if ε a = ε b then (if d = b then E a b * E c a else 0) else 0)
          - (if ε a = ε b then (if b = c then E a d * E b a else 0) else 0)) := by sorry
