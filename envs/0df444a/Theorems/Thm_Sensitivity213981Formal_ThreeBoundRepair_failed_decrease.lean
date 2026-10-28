-- Prove2me | Theorems.Thm_Sensitivity213981Formal_ThreeBoundRepair_failed_decrease
-- name    : Sensitivity213981Formal.ThreeBoundRepair.failed_decrease
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-26T18:26:28.693447+00:00
-- url     : https://prove2.me/theorems/e8b2144c-399b-40bc-86aa-bec73290c0a8
-- title:
--   A single-bit guard-count decrease removes exactly one selected failure
-- statement:
--   Fix a stage, a family, a row \(v\), and a level \(l\). If flipping \(((w,c),a)\) strictly decreases the row's failed-guard count, then the selected edge is \(v\to w\) with label \(c\), its guard child changes from true to false, and
--   \[
--   |\operatorname{failed}_l(x,v)|=
--   |\operatorname{failed}_l(x^{\{((w,c),a)\}},v)|+1.
--   \]
--   Thus a strict decrease has a unique location and decreases the count by exactly one.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; GradedRepairCover.lean, lines 47–88.

import Definitions.Def_Sensitivity213981Formal_GuardAugmentation
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_Supplement_GradedPositiveBoundary
import Definitions.Def_Sensitivity213981Formal_Supplement_Q2Enumeration
import Definitions.Def_Sensitivity213981Formal_WitnessLifting
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Sort
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem Sensitivity213981Formal.ThreeBoundRepair.failed_decrease :
∀ {L I V : Type} [inst : Fintype.{0} V] (S : Sensitivity213981Formal.ThreeBoundWitness.Stage L I V)
  (F : L → (I → Bool) → Bool) (l : L) (x : Prod.{0, 0} (Prod.{0, 0} V Bool) I → Bool) (v w : V) (c : Bool) (a : I)
  (hdec :
    @LT.lt.{0} Nat instLTNat
      (@Finset.card.{0} V
        (@Sensitivity213981Formal.ThreeBoundWitness.failed L I V inst S F l
          (@OAI.Paper320.flip (Prod.{0, 0} (Prod.{0, 0} V Bool) I) x
            (@Singleton.singleton.{0, 0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I)
              (Finset.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I))
              (@Finset.instSingleton.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I))
              (@Prod.mk.{0, 0} (Prod.{0, 0} V Bool) I (@Prod.mk.{0, 0} V Bool w c) a)))
          v))
      (@Finset.card.{0} V (@Sensitivity213981Formal.ThreeBoundWitness.failed L I V inst S F l x v))),
  And (@Sensitivity213981Formal.ThreeBoundWitness.Stage.Adj L I V S v w)
    (And (@Eq.{1} Bool (@Sensitivity213981Formal.ThreeBoundWitness.Stage.label L I V S v w) c)
      (And
        (@Eq.{1} Bool
          (F (@Sensitivity213981Formal.ThreeBoundWitness.Stage.guard L I V S l)
            (@Sensitivity213981Formal.ThreeBoundWitness.child I V x w c))
          Bool.true)
        (And
          (@Eq.{1} Bool
            (F (@Sensitivity213981Formal.ThreeBoundWitness.Stage.guard L I V S l)
              (@OAI.Paper320.flip I (@Sensitivity213981Formal.ThreeBoundWitness.child I V x w c)
                (@Singleton.singleton.{0, 0} I (Finset.{0} I) (@Finset.instSingleton.{0} I) a)))
            Bool.false)
          (@Eq.{1} Nat (@Finset.card.{0} V (@Sensitivity213981Formal.ThreeBoundWitness.failed L I V inst S F l x v))
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@Finset.card.{0} V
                (@Sensitivity213981Formal.ThreeBoundWitness.failed L I V inst S F l
                  (@OAI.Paper320.flip (Prod.{0, 0} (Prod.{0, 0} V Bool) I) x
                    (@Singleton.singleton.{0, 0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I)
                      (Finset.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I))
                      (@Finset.instSingleton.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I))
                      (@Prod.mk.{0, 0} (Prod.{0, 0} V Bool) I (@Prod.mk.{0, 0} V Bool w c) a)))
                  v))
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))) := by sorry
