-- Prove2me | Theorems.Thm_Sensitivity213981Formal_ThreeBoundOrdinary5591_ordinaryAExpr_bound
-- name    : Sensitivity213981Formal.ThreeBoundOrdinary5591.ordinaryAExpr_bound
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T01:33:42.13859+00:00
-- url     : https://prove2.me/theorems/d535666c-7fef-4916-a5d0-42990424caad
-- title:
--   ordinary AExpr bound — Boolean sensitivity certificate
-- statement:
--   The following universally quantified assertion holds for the finite sets, Boolean families, tournament data, and profile coordinates defined in the imported interfaces. Each binder specifies the domain of its variable, and bracketed conditions specify finite or ordered structures.
--
--   $$
--   \forall n:\mathbb N,\quad \forall k:\mathbb N,\quad \forall I:\mathcal U,\quad \bigl[\mathrm{finite}(I)\bigr]\;\forall S:\operatorname{Witness.Stage}\bigl(\{0,\ldots,n-1\}, I, \{0,\ldots,k-1\}\bigr),\quad \forall T:\operatorname{Paper320.Tournament}\bigl(k\bigr),\quad \forall \mathit{ell}:\left(\{0,\ldots,k-1\}\to \left(\{0,\ldots,k-1\}\to \{0,\ldots,2-1\}\right)\right),\quad \bigl(\forall v:\{0,\ldots,k-1\},\quad \forall w:\{0,\ldots,k-1\},\quad \bigl(\operatorname{Digraph.Adj}\bigl(\operatorname{Tournament.toDigraph}\bigl(T\bigr), v, w\bigr) \Longleftrightarrow \operatorname{Stage.Adj}\bigl(S, v, w\bigr)\bigr)\Longrightarrow \bigl(\forall v:\{0,\ldots,k-1\},\quad \forall w:\{0,\ldots,k-1\},\quad \bigl(\operatorname{DFunLike.coe}\bigl(\operatorname{finTwoEquiv}, \mathit{ell}\bigl(v, w\bigr)\bigr) = \operatorname{Stage.label}\bigl(S, v, w\bigr)\bigr)\Longrightarrow \bigl(\operatorname{Ordinary5591.LabelCaps}\bigl(T, \mathit{ell}\bigr)\Longrightarrow \forall F:\left(\{0,\ldots,n-1\}\to \left(\left(I\to \mathbb B\right)\to \mathbb B\right)\right),\quad \bigl(\operatorname{Profiles.Nested}\bigl(F\bigr)\Longrightarrow \forall \mathit{ta}:\{0,\ldots,n-1\},\quad \forall \mathit{tb}:\{0,\ldots,n-1\},\quad \forall \mathit{ga}:\{0,\ldots,n-1\},\quad \forall \mathit{gb}:\{0,\ldots,n-1\},\quad \bigl(\bigl(\mathit{ta} \le \mathit{tb}\bigr)\Longrightarrow \bigl(\bigl(\mathit{gb} \le \mathit{ga}\bigr)\Longrightarrow \bigl(\bigl(\mathit{ga} \le \mathit{ta}\bigr)\Longrightarrow \forall \mathit{qa}:\mathbb N,\quad \forall q:\mathbb N,\quad \bigl(\bigl(q \le \mathit{qa}\bigr)\Longrightarrow \bigl(\bigl(4 \le q\bigr)\Longrightarrow \bigl(\bigl(q \le 8\bigr)\Longrightarrow \forall v:\operatorname{FullProfile.Profile}\bigl(n\bigr),\quad \bigl(\operatorname{FullProfile.Upper}\bigl(F, v\bigr)\Longrightarrow \forall x:\left(\{0,\ldots,k-1\}\times \mathbb B\times I\to \mathbb B\right),\quad \bigl(\bigl(\operatorname{Conditional.ordinaryParent}\bigl(S, F, \mathit{ta}, \mathit{ga}, \mathit{qa}, x\bigr) = \mathsf{false}\bigr)\Longrightarrow \bigl(|\operatorname{Profiles.flipsTo}\bigl(\operatorname{Conditional.ordinaryParent}\bigl(S, F, \mathit{tb}, \mathit{gb}, q\bigr), \mathsf{true}, x\bigr)| \le \operatorname{Expr.eval}\bigl(v, \operatorname{Numeric.ordinaryAExpr}\bigl(n, \operatorname{Ordinary5591.numericCaps}, \mathit{ta}, \mathit{ga}, \mathit{qa}, \mathit{tb}, \mathit{gb}, q\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)
--   $$
--
--   Here $\mathbb B=\{\mathsf{false},\mathsf{true}\}$; $\mathcal P_{\mathrm{fin}}(X)$ denotes the finite subsets of $X$. Named functions and predicates refer to their definitions in the cited source. This result supplies the corresponding ordinary AExpr bound step in the verified $22$-level sensitivity construction.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Ordinary5591Numeric.lean, lines 64–99.

import Definitions.Def_Sensitivity213981Formal_HeadCostExpressions
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_Ordinary5591Numeric
import Definitions.Def_Sensitivity213981Formal_OrdinaryParentBridge
import Definitions.Def_Sensitivity213981Formal_ProfileClosures
import Definitions.Def_Sensitivity213981Formal_Q2RawExpressions
import Definitions.Def_Sensitivity213981Formal_Supplement_NumericExpressions
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
import Mathlib.Algebra.Order.Ring.Nat
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
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Sort
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

theorem Sensitivity213981Formal.ThreeBoundOrdinary5591.ordinaryAExpr_bound :
∀ {n k : Nat} {I : Type} [inst : Fintype.{0} I] (S : Sensitivity213981Formal.ThreeBoundWitness.Stage (Fin n) I (Fin k))
  (T : Sensitivity213981Formal.ThreeBoundOrdinaryArchive.OAI.Paper320.Tournament k)
  (ell : Fin k → Fin k → Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
  (hAdj :
    ∀ (v w : Fin k),
      Iff
        (@Digraph.Adj.{0} (Fin k)
          (@Sensitivity213981Formal.ThreeBoundOrdinaryArchive.OAI.Paper320.Tournament.toDigraph k T) v w)
        (@Sensitivity213981Formal.ThreeBoundWitness.Stage.Adj (Fin n) I (Fin k) S v w))
  (hLabel :
    ∀ (v w : Fin k),
      @Eq.{1} Bool
        (@DFunLike.coe.{1, 1, 1} (Equiv.{1, 1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Bool)
          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (fun (x : Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) => Bool)
          (@EquivLike.toFunLike.{1, 1, 1}
            (Equiv.{1, 1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Bool)
            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Bool
            (@Equiv.instEquivLike.{1, 1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Bool))
          finTwoEquiv (ell v w))
        (@Sensitivity213981Formal.ThreeBoundWitness.Stage.label (Fin n) I (Fin k) S v w))
  (hCaps : @Sensitivity213981Formal.ThreeBoundOrdinary5591.LabelCaps k T ell) (F : Fin n → (I → Bool) → Bool)
  (hF :
    @Sensitivity213981Formal.ThreeBoundProfiles.Nested (Fin n) I
      (@PartialOrder.toPreorder.{0} (Fin n) (@Fin.instPartialOrder n)) F)
  (ta tb ga gb : Fin n) (ht : @LE.le.{0} (Fin n) (@instLEFin n) ta tb) (hg : @LE.le.{0} (Fin n) (@instLEFin n) gb ga)
  (hga : @LE.le.{0} (Fin n) (@instLEFin n) ga ta) (qa q : Nat) (hq : @LE.le.{0} Nat instLENat q qa)
  (hq4 : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) q)
  (hq8 : @LE.le.{0} Nat instLENat q (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
  (v : Sensitivity213981Formal.ThreeBoundFullProfile.Profile n)
  (hv : @Sensitivity213981Formal.ThreeBoundFullProfile.Upper n I inst F v)
  (x : Prod.{0, 0} (Prod.{0, 0} (Fin k) Bool) I → Bool)
  (hx :
    @Eq.{1} Bool
      (@Sensitivity213981Formal.ThreeBoundConditional.ordinaryParent (Fin n) I (Fin k) (Fin.fintype k) S F ta ga qa x)
      Bool.false),
  @LE.le.{0} Nat instLENat
    (@Finset.card.{0} (Prod.{0, 0} (Prod.{0, 0} (Fin k) Bool) I)
      (@Sensitivity213981Formal.ThreeBoundProfiles.flipsTo (Prod.{0, 0} (Prod.{0, 0} (Fin k) Bool) I)
        (@instFintypeProd.{0, 0} (Prod.{0, 0} (Fin k) Bool) I
          (@instFintypeProd.{0, 0} (Fin k) Bool (Fin.fintype k) Bool.fintype) inst)
        (@Sensitivity213981Formal.ThreeBoundConditional.ordinaryParent (Fin n) I (Fin k) (Fin.fintype k) S F tb gb q)
        Bool.true x))
    (@Sensitivity213981Formal.ThreeBoundNumeric.Expr.eval n v
      (Sensitivity213981Formal.ThreeBoundNumeric.ordinaryAExpr n
        Sensitivity213981Formal.ThreeBoundOrdinary5591.numericCaps (@Fin.val n ta) (@Fin.val n ga) qa (@Fin.val n tb)
        (@Fin.val n gb) q)) := by sorry
