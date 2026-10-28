-- Prove2me | Theorems.Thm_Sensitivity213981Formal_ThreeBoundConditional_ordinaryGuardBits_card_le
-- name    : Sensitivity213981Formal.ThreeBoundConditional.ordinaryGuardBits_card_le
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-26T19:33:16.940338+00:00
-- url     : https://prove2.me/theorems/480c1572-bf81-4e1c-8402-50b6fa9c98c7
-- title:
--   Passing guards contribute at most one upward profile each
-- statement:
--   Fix a stage, an input, and a row \(v\). Let \(d^+(v)\) be its outgoing degree and \(f_{g_j}(v)\) the number of failed guards at level \(g_j\). If the child upward profile \(A_F(g_j,g_i)\) is bounded by \(a\), then the ordinary guard-destruction bit set satisfies
--   \[
--   |\operatorname{ordinaryGuardBits}|
--   \le \bigl(d^+(v)-f_{g_j}(v)\bigr)a.
--   \]
--   Each contributing child is selected by a currently passing guard. This bounds the guard part of a downward parent profile.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; ConditionalOrdinary.lean, lines 165–180.

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

theorem Sensitivity213981Formal.ThreeBoundConditional.ordinaryGuardBits_card_le :
∀ {L I V : Type} [LinearOrder.{0} L] [inst : Fintype.{0} I] [inst_1 : Fintype.{0} V]
  (S : Sensitivity213981Formal.ThreeBoundWitness.Stage L I V) (F : L → (I → Bool) → Bool) (gi gj : L)
  (x : Prod.{0, 0} (Prod.{0, 0} V Bool) I → Bool) (v : V) (a : Nat)
  (ha : @Sensitivity213981Formal.ThreeBoundProfiles.ABound L I inst F gj gi a),
  @LE.le.{0} Nat instLENat
    (@Finset.card.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I)
      (@Sensitivity213981Formal.ThreeBoundConditional.ordinaryGuardBits L I V inst inst_1 S F gi gj x v))
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
      (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
        (@Finset.card.{0} V (@Sensitivity213981Formal.ThreeBoundPositive.outgoing L I V inst_1 S v))
        (@Finset.card.{0} V (@Sensitivity213981Formal.ThreeBoundConditional.guardFailures L I V inst_1 S F gj x v)))
      a) := by sorry
