-- Prove2me | Theorems.Thm_Sensitivity213981Formal_ThreeBoundOrdinaryArchive_ZT_targets_card_positive_marked
-- name    : Sensitivity213981Formal.ThreeBoundOrdinaryArchive.ZT.targets_card_positive_marked
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-26T18:50:27.000238+00:00
-- url     : https://prove2.me/theorems/48e61c49-e89d-4d8c-96aa-eedf5f7422ac
-- title:
--   targets card positive marked — Boolean sensitivity certificate
-- statement:
--   The following universally quantified assertion holds for the finite sets, Boolean families, tournament data, and profile coordinates defined in the imported interfaces. Each binder specifies the domain of its variable, and bracketed conditions specify finite or ordered structures.
--
--   $$
--   \forall n:\mathbb N,\quad \forall k:\mathbb N,\quad \forall I:\mathcal U,\quad \bigl[\mathrm{finite}(I)\bigr]\;\forall T:\operatorname{Paper320.Tournament}\bigl(k\bigr),\quad \forall \mathit{label}:\left(\{0,\ldots,k-1\}\to \left(\{0,\ldots,k-1\}\to \{0,\ldots,2-1\}\right)\right),\quad \forall F:\left(\{0,\ldots,n-1\}\to \left(\left(I\to \mathbb B\right)\to \mathbb B\right)\right),\quad \bigl(\operatorname{Paper320.NestedFamily}\bigl(F\bigr)\Longrightarrow \forall t:\{0,\ldots,n-1\},\quad \forall g:\{0,\ldots,n-1\},\quad \bigl(\bigl(g \le t\bigr)\Longrightarrow \forall q:\mathbb N,\quad \forall r:\mathbb N,\quad \forall w:\mathbb N,\quad \bigl(\operatorname{ZT.MarkedCardBound}\bigl(T, \mathit{label}, q, r, 0, \bigl(r\cdot \bigl(q+1\bigr)\bigr), w\bigr)\Longrightarrow \forall x:\left(\{0,\ldots,k-1\}\times \{0,\ldots,2-1\}\times I\to \mathbb B\right),\quad \bigl(\bigl(r \le |\operatorname{SensitivityQ.positiveTargets}\bigl(T, \mathit{label}, F, t, g, q, x, \operatorname{of\_decide\_eq\_true}\bigl(\operatorname{id}\bigl(\operatorname{Eq.refl}\bigl(\mathsf{true}\bigr)\bigr)\bigr)\bigr)|\bigr)\Longrightarrow \bigl(|\operatorname{Sensitivity2075.tolerantTargets}\bigl(T, \mathit{label}, F, t, g, q, x\bigr)| < \bigl(w+r\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)
--   $$
--
--   Here $\mathbb B=\{\mathsf{false},\mathsf{true}\}$; $\mathcal P_{\mathrm{fin}}(X)$ denotes the finite subsets of $X$. Named functions and predicates refer to their definitions in the cited source. This result supplies the corresponding targets card positive marked step in the verified $22$-level sensitivity construction.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; ArchivedOrdinaryCaps.lean, lines 772–791.

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

theorem Sensitivity213981Formal.ThreeBoundOrdinaryArchive.ZT.targets_card_positive_marked :
∀ {n k : Nat} {I : Type} [Fintype.{0} I]
  (T : Sensitivity213981Formal.ThreeBoundOrdinaryArchive.OAI.Paper320.Tournament k)
  (label : Fin k → Fin k → Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
  (F : Fin n → (I → Bool) → Bool)
  (hF : @Sensitivity213981Formal.ThreeBoundOrdinaryArchive.OAI.Paper320.NestedFamily n I F) (t g : Fin n)
  (hgt : @LE.le.{0} (Fin n) (@instLEFin n) g t) (q r w : Nat)
  (hcap :
    @Sensitivity213981Formal.ThreeBoundOrdinaryArchive.ZT.MarkedCardBound k T label q r
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) r
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) q
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      w)
  (x : Prod.{0, 0} (Prod.{0, 0} (Fin k) (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) I → Bool)
  (hr :
    @LE.le.{0} Nat instLENat r
      (@Finset.card.{0} (Fin k)
        (@Sensitivity213981Formal.ThreeBoundOrdinaryArchive.SensitivityQ.positiveTargets n k
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
              (@Eq.refl.{1} Bool Bool.true)))))),
  @LT.lt.{0} Nat instLTNat
    (@Finset.card.{0} (Fin k)
      (@Sensitivity213981Formal.ThreeBoundOrdinaryArchive.Sensitivity2075.tolerantTargets n k
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) I T label F t g q x))
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) w r) := by sorry
