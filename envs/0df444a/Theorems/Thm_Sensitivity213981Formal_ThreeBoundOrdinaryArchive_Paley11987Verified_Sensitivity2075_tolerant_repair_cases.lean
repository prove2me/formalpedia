-- Prove2me | Theorems.Thm_Sensitivity213981Formal_ThreeBoundOrdinaryArchive_Paley11987Verified_Sensitivity2075_tolerant_repair_cases
-- name    : Sensitivity213981Formal.ThreeBoundOrdinaryArchive.Paley11987Verified.Sensitivity2075.tolerant_repair_cases
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-26T18:55:07.619979+00:00
-- url     : https://prove2.me/theorems/3804cf9e-d7e7-42a3-acdf-a282f96a10a3
-- title:
--   A single-bit repair of a tolerant row has two possible causes
-- statement:
--   Consider a tolerant row \(i\) in the recursive tournament construction, with target level \(A\), guard level \(G\), and tolerance \(q\). Suppose the row is false before a flip at child coordinate \(((j,c),a)\), and true afterwards. Then exactly the following alternatives cover the repair: the flip is in row \(i\)'s own child (\(j=i\)) and changes its unique missing target from false to true; or \(i\) has exactly \(q+1\) failed guards and the flip changes a selected outgoing guard from true to false. In the guard case,
--   \[
--   T(i,j),\qquad c=\ell(i,j).
--   \]
--   The theorem identifies the positions and child boundaries to which an upward-sensitive bit may be charged.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; ArchivedOrdinaryRepair.lean, lines 181–234.

import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_Supplement_ArchivedOrdinaryDefinitions
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.GroupWithZero.Units.Equiv
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.NumberTheory.JacobiSum.Basic
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem Sensitivity213981Formal.ThreeBoundOrdinaryArchive.Paley11987Verified.Sensitivity2075.tolerant_repair_cases :
∀ {n k r : Nat} {I : Type} (T : Sensitivity213981Formal.ThreeBoundOrdinaryArchive.OAI.Paper320.Tournament k)
  (label : Fin k → Fin k → Fin r) (F : Fin n → (I → Bool) → Bool) (A G : Fin n) (q : Nat)
  (x : Prod.{0, 0} (Prod.{0, 0} (Fin k) (Fin r)) I → Bool) (i j : Fin k) (c : Fin r) (a : I)
  (hoff :
    @Eq.{1} Bool
      (@Sensitivity213981Formal.ThreeBoundOrdinaryArchive.Sensitivity2075.tolerantRow n k r I T label F A G q x i)
      Bool.false)
  (hon :
    @Eq.{1} Bool
      (@Sensitivity213981Formal.ThreeBoundOrdinaryArchive.Sensitivity2075.tolerantRow n k r I T label F A G q
        (@OAI.Paper320.flip (Prod.{0, 0} (Prod.{0, 0} (Fin k) (Fin r)) I) x
          (@Singleton.singleton.{0, 0} (Prod.{0, 0} (Prod.{0, 0} (Fin k) (Fin r)) I)
            (Finset.{0} (Prod.{0, 0} (Prod.{0, 0} (Fin k) (Fin r)) I))
            (@Finset.instSingleton.{0} (Prod.{0, 0} (Prod.{0, 0} (Fin k) (Fin r)) I))
            (@Prod.mk.{0, 0} (Prod.{0, 0} (Fin k) (Fin r)) I (@Prod.mk.{0, 0} (Fin k) (Fin r) j c) a)))
        i)
      Bool.true),
  Or
    (And
      (@Membership.mem.{0, 0} (Fin k) (Finset.{0} (Fin k))
        (@SetLike.instMembership.{0, 0} (Finset.{0} (Fin k)) (Fin k) (@Finset.instSetLike.{0} (Fin k)))
        (@Sensitivity213981Formal.ThreeBoundOrdinaryArchive.Sensitivity2075.tolerantTargets n k r I T label F A G q x)
        i)
      (And (@Eq.{1} (Fin k) j i)
        (And
          (@Eq.{1} Bool
            (F A (@Sensitivity213981Formal.ThreeBoundOrdinaryArchive.OAI.Paper320.recursiveChild k r I x j c))
            Bool.false)
          (@Eq.{1} Bool
            (F A
              (@OAI.Paper320.flip I
                (@Sensitivity213981Formal.ThreeBoundOrdinaryArchive.OAI.Paper320.recursiveChild k r I x j c)
                (@Singleton.singleton.{0, 0} I (Finset.{0} I) (@Finset.instSingleton.{0} I) a)))
            Bool.true))))
    (And
      (@Membership.mem.{0, 0} (Fin k) (Finset.{0} (Fin k))
        (@SetLike.instMembership.{0, 0} (Finset.{0} (Fin k)) (Fin k) (@Finset.instSetLike.{0} (Fin k)))
        (@Sensitivity213981Formal.ThreeBoundOrdinaryArchive.Sensitivity2075.tolerantGuards n k r I T label F A G q x) i)
      (And
        (@Digraph.Adj.{0} (Fin k)
          (@Sensitivity213981Formal.ThreeBoundOrdinaryArchive.OAI.Paper320.Tournament.toDigraph k T) i j)
        (And (@Eq.{1} (Fin r) c (label i j))
          (And
            (@Eq.{1} Bool
              (F G (@Sensitivity213981Formal.ThreeBoundOrdinaryArchive.OAI.Paper320.recursiveChild k r I x j c))
              Bool.true)
            (@Eq.{1} Bool
              (F G
                (@OAI.Paper320.flip I
                  (@Sensitivity213981Formal.ThreeBoundOrdinaryArchive.OAI.Paper320.recursiveChild k r I x j c)
                  (@Singleton.singleton.{0, 0} I (Finset.{0} I) (@Finset.instSingleton.{0} I) a)))
              Bool.false))))) := by sorry
