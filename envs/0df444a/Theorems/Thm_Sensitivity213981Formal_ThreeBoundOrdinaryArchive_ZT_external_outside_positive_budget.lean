-- Prove2me | Theorems.Thm_Sensitivity213981Formal_ThreeBoundOrdinaryArchive_ZT_external_outside_positive_budget
-- name    : Sensitivity213981Formal.ThreeBoundOrdinaryArchive.ZT.external_outside_positive_budget
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-26T18:57:44.660014+00:00
-- url     : https://prove2.me/theorems/193ac5bb-f112-4c02-a1c9-288e558de8e8
-- title:
--   Positive candidates force some external guard arcs to stay inside
-- statement:
--   In a nested Boolean construction on a labeled tournament, let \(P\) be the positive target candidates and \(G\) the guard candidates at tolerance \(q\). Let \(E\) be the external guard arcs, meaning failed-guard arcs from \(G\) whose heads lie outside \(G\), and let \(E_{\neg P}\) be those whose heads also lie outside \(P\). Then
--   \[
--   |E_{\neg P}|+
--   \left(|P||G|+\binom{|P|}{2}-q|P|\right)_+\le |E|,
--   \]
--   where \((z)_+=\max(z,0)\). This forces enough external arcs to land on positive heads to account for the mixed internal-edge budget.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; ArchivedOrdinaryPositive.lean, lines 1373–1426.

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

theorem Sensitivity213981Formal.ThreeBoundOrdinaryArchive.ZT.external_outside_positive_budget :
∀ {n k : Nat} {I : Type} [Fintype.{0} I]
  (T : Sensitivity213981Formal.ThreeBoundOrdinaryArchive.OAI.Paper320.Tournament k)
  (label : Fin k → Fin k → Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
  (F : Fin n → (I → Bool) → Bool)
  (hF : @Sensitivity213981Formal.ThreeBoundOrdinaryArchive.OAI.Paper320.NestedFamily n I F) (t g : Fin n)
  (hgt : @LE.le.{0} (Fin n) (@instLEFin n) g t) (q : Nat)
  (x : Prod.{0, 0} (Prod.{0, 0} (Fin k) (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) I → Bool),
  have G : Finset.{0} (Fin k) :=
    @Sensitivity213981Formal.ThreeBoundOrdinaryArchive.Sensitivity2075.tolerantGuards n k
      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) I T label F t g q x;
  have P : Finset.{0} (Fin k) :=
    @Sensitivity213981Formal.ThreeBoundOrdinaryArchive.SensitivityQ.positiveTargets n k
      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) I T label F t g q x
      (@of_decide_eq_true
        (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (Nat.decLt (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@id.{0}
          (@Eq.{1} Bool
            (@Decidable.decide
              (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (Nat.decLt (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
            Bool.true)
          (@Eq.refl.{1} Bool Bool.true)));
  have S : Finset.{0} (Prod.{0, 0} (Fin k) (Fin k)) :=
    @Sensitivity213981Formal.ThreeBoundOrdinaryArchive.ZT.externalGuardArcs n k I T label F t g q x;
  @LE.le.{0} Nat instLENat
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@Finset.card.{0} (Prod.{0, 0} (Fin k) (Fin k))
        (@Finset.filter.{0} (Prod.{0, 0} (Fin k) (Fin k))
          (fun (e : Prod.{0, 0} (Fin k) (Fin k)) =>
            Not
              (@Membership.mem.{0, 0} (Fin k) (Finset.{0} (Fin k))
                (@SetLike.instMembership.{0, 0} (Finset.{0} (Fin k)) (Fin k) (@Finset.instSetLike.{0} (Fin k))) P
                (@Prod.snd.{0, 0} (Fin k) (Fin k) e)))
          (fun (a : Prod.{0, 0} (Fin k) (Fin k)) =>
            @instDecidableNot
              (@Membership.mem.{0, 0} (Fin k) (Finset.{0} (Fin k))
                (@SetLike.instMembership.{0, 0} (Finset.{0} (Fin k)) (Fin k) (@Finset.instSetLike.{0} (Fin k))) P
                (@Prod.snd.{0, 0} (Fin k) (Fin k) a))
              (@Finset.decidableMem.{0} (Fin k) (instDecidableEqFin k) (@Prod.snd.{0, 0} (Fin k) (Fin k) a) P))
          S))
      (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (@Finset.card.{0} (Fin k) P)
            (@Finset.card.{0} (Fin k) G))
          (Nat.choose (@Finset.card.{0} (Fin k) P) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) q (@Finset.card.{0} (Fin k) P))))
    (@Finset.card.{0} (Prod.{0, 0} (Fin k) (Fin k)) S) := by sorry
