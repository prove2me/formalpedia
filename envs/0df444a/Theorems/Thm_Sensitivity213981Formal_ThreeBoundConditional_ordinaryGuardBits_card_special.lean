-- Prove2me | Theorems.Thm_Sensitivity213981Formal_ThreeBoundConditional_ordinaryGuardBits_card_special
-- name    : Sensitivity213981Formal.ThreeBoundConditional.ordinaryGuardBits_card_special
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-26T19:33:02.800748+00:00
-- url     : https://prove2.me/theorems/60be7d67-99e7-4c1b-91f1-04149d39885d
-- title:
--   A conditioned passing guard improves one term of the guard cost
-- statement:
--   In the ordinary guard-bit setting, suppose a particular passing guard selects a child that is also true at level \(g_k\). If \(A_F(g_j,g_i)\le a\) and \(P_F(g_k,g_j,g_i)\le p\), then
--   \[
--   |\operatorname{ordinaryGuardBits}|
--   \le\bigl(d^+(v)-f_{g_j}(v)-1\bigr)a+p.
--   \]
--   The additional true condition replaces one ordinary upward charge by the conditional charge \(p\).
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; ConditionalOrdinary.lean, lines 182–211.

import Definitions.Def_Sensitivity213981Formal_ConditionalOrdinary
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_Supplement_GradedPositiveBoundary
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem Sensitivity213981Formal.ThreeBoundConditional.ordinaryGuardBits_card_special :
∀ {L I V : Type} [LinearOrder.{0} L] [inst : Fintype.{0} I] [inst_1 : Fintype.{0} V]
  (S : Sensitivity213981Formal.ThreeBoundWitness.Stage L I V) (F : L → (I → Bool) → Bool) (gi gj gk : L)
  (x : Prod.{0, 0} (Prod.{0, 0} V Bool) I → Bool) (v w : V) (a p : Nat)
  (ha : @Sensitivity213981Formal.ThreeBoundProfiles.ABound L I inst F gj gi a)
  (hp : @Sensitivity213981Formal.ThreeBoundProfiles.PBound L I inst F gk gj gi p)
  (hw :
    @Membership.mem.{0, 0} V (Finset.{0} V)
      (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V))
      (@Sensitivity213981Formal.ThreeBoundConditional.passingGuards L I V inst_1 S F gj x v) w)
  (hk :
    @Eq.{1} Bool
      (F gk
        (@Sensitivity213981Formal.ThreeBoundWitness.child I V x w
          (@Sensitivity213981Formal.ThreeBoundWitness.Stage.label L I V S v w)))
      Bool.true),
  @LE.le.{0} Nat instLENat
    (@Finset.card.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I)
      (@Sensitivity213981Formal.ThreeBoundConditional.ordinaryGuardBits L I V inst inst_1 S F gi gj x v))
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
          (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
            (@Finset.card.{0} V (@Sensitivity213981Formal.ThreeBoundPositive.outgoing L I V inst_1 S v))
            (@Finset.card.{0} V (@Sensitivity213981Formal.ThreeBoundConditional.guardFailures L I V inst_1 S F gj x v)))
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        a)
      p) := by sorry
