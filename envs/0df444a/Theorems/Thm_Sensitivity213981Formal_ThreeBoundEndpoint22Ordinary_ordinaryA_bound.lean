-- Prove2me | Theorems.Thm_Sensitivity213981Formal_ThreeBoundEndpoint22Ordinary_ordinaryA_bound
-- name    : Sensitivity213981Formal.ThreeBoundEndpoint22Ordinary.ordinaryA_bound
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T01:51:53.41332+00:00
-- url     : https://prove2.me/theorems/5ac16048-cd6c-4113-a8ef-e00dc2c0c39e
-- title:
--   ordinary A bound — Boolean sensitivity certificate
-- statement:
--   The following universally quantified assertion holds for the finite sets, Boolean families, tournament data, and profile coordinates defined in the imported interfaces. Each binder specifies the domain of its variable, and bracketed conditions specify finite or ordered structures.
--
--   $$
--   \forall I:\mathcal U,\quad \bigl[\mathrm{finite}(I)\bigr]\;\forall \mathit{Adj}:\left(\{0,\ldots,5591-1\}\to \left(\{0,\ldots,5591-1\}\to \mathrm{Prop}\right)\right),\quad \bigl(\forall w:\{0,\ldots,5591-1\},\quad \neg \mathit{Adj}\bigl(w, w\bigr)\Longrightarrow \forall \mathit{label}:\left(\{0,\ldots,5591-1\}\to \left(\{0,\ldots,5591-1\}\to \mathbb B\right)\right),\quad \forall T:\operatorname{Paper320.Tournament}\bigl(5591\bigr),\quad \forall \mathit{ell}:\left(\{0,\ldots,5591-1\}\to \left(\{0,\ldots,5591-1\}\to \{0,\ldots,2-1\}\right)\right),\quad \bigl(\forall v:\{0,\ldots,5591-1\},\quad \forall w:\{0,\ldots,5591-1\},\quad \bigl(\operatorname{Digraph.Adj}\bigl(\operatorname{Tournament.toDigraph}\bigl(T\bigr), v, w\bigr) \Longleftrightarrow \mathit{Adj}\bigl(v, w\bigr)\bigr)\Longrightarrow \bigl(\forall v:\{0,\ldots,5591-1\},\quad \forall w:\{0,\ldots,5591-1\},\quad \bigl(\operatorname{DFunLike.coe}\bigl(\operatorname{finTwoEquiv}, \mathit{ell}\bigl(v, w\bigr)\bigr) = \mathit{label}\bigl(v, w\bigr)\bigr)\Longrightarrow \bigl(\operatorname{Ordinary5591.LabelCaps}\bigl(T, \mathit{ell}\bigr)\Longrightarrow \forall p:\{0,\ldots,4-1\},\quad \forall F:\left(\{0,\ldots,22-1\}\to \left(\left(I\to \mathbb B\right)\to \mathbb B\right)\right),\quad \bigl(\operatorname{Profiles.Nested}\bigl(F\bigr)\Longrightarrow \forall v:\operatorname{FullProfile.Profile}\bigl(22\bigr),\quad \bigl(\operatorname{FullProfile.Upper}\bigl(F, v\bigr)\Longrightarrow \forall i:\{0,\ldots,22-1\},\quad \forall j:\{0,\ldots,22-1\},\quad \bigl(\bigl(i \le j\bigr)\Longrightarrow \bigl(\bigl(4 \le \operatorname{Entry.tolerance}\bigl(\operatorname{Endpoint22.recipe}\bigl(p, j\bigr)\bigr)\bigr)\Longrightarrow \operatorname{Profiles.ABound}\bigl(\operatorname{Witness.parent}\bigl(\operatorname{MinMaxRecipe.stage}\bigl(\operatorname{Sensitivity5591Endpoint22.recipe}\bigl(\mathit{Adj}, \mathit{loopless}, \mathit{label}, p\bigr), F\bigr), F\bigr), i, j, \operatorname{Expr.eval}\bigl(v, \operatorname{Numeric.ordinaryAExpr}\bigl(22, \operatorname{Ordinary5591.numericCaps}, \operatorname{Entry.lowerAt}\bigl(\operatorname{Endpoint22.recipe}\bigl(p, i\bigr), 0\bigr), \operatorname{Entry.guard}\bigl(\operatorname{Endpoint22.recipe}\bigl(p, i\bigr)\bigr), \operatorname{Entry.tolerance}\bigl(\operatorname{Endpoint22.recipe}\bigl(p, i\bigr)\bigr), \operatorname{Entry.lowerAt}\bigl(\operatorname{Endpoint22.recipe}\bigl(p, j\bigr), 0\bigr), \operatorname{Entry.guard}\bigl(\operatorname{Endpoint22.recipe}\bigl(p, j\bigr)\bigr), \operatorname{Entry.tolerance}\bigl(\operatorname{Endpoint22.recipe}\bigl(p, j\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)
--   $$
--
--   Here $\mathbb B=\{\mathsf{false},\mathsf{true}\}$; $\mathcal P_{\mathrm{fin}}(X)$ denotes the finite subsets of $X$. Named functions and predicates refer to their definitions in the cited source. This result supplies the corresponding ordinary A bound step in the verified $22$-level sensitivity construction.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22OrdinaryA.lean, lines 23–52.

import Definitions.Def_Sensitivity213981Formal_Endpoint22PairData
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_Ordinary5591Numeric
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

theorem Sensitivity213981Formal.ThreeBoundEndpoint22Ordinary.ordinaryA_bound :
∀ {I : Type} [inst : Fintype.{0} I]
  (Adj :
    Fin (@OfNat.ofNat.{0} Nat (nat_lit 5591) (instOfNatNat (nat_lit 5591))) →
      Fin (@OfNat.ofNat.{0} Nat (nat_lit 5591) (instOfNatNat (nat_lit 5591))) → Prop)
  (loopless : ∀ (w : Fin (@OfNat.ofNat.{0} Nat (nat_lit 5591) (instOfNatNat (nat_lit 5591)))), Not (Adj w w))
  (label :
    Fin (@OfNat.ofNat.{0} Nat (nat_lit 5591) (instOfNatNat (nat_lit 5591))) →
      Fin (@OfNat.ofNat.{0} Nat (nat_lit 5591) (instOfNatNat (nat_lit 5591))) → Bool)
  (T :
    Sensitivity213981Formal.ThreeBoundOrdinaryArchive.OAI.Paper320.Tournament
      (@OfNat.ofNat.{0} Nat (nat_lit 5591) (instOfNatNat (nat_lit 5591))))
  (ell :
    Fin (@OfNat.ofNat.{0} Nat (nat_lit 5591) (instOfNatNat (nat_lit 5591))) →
      Fin (@OfNat.ofNat.{0} Nat (nat_lit 5591) (instOfNatNat (nat_lit 5591))) →
        Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
  (hAdj :
    ∀ (v w : Fin (@OfNat.ofNat.{0} Nat (nat_lit 5591) (instOfNatNat (nat_lit 5591)))),
      Iff
        (@Digraph.Adj.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5591) (instOfNatNat (nat_lit 5591))))
          (@Sensitivity213981Formal.ThreeBoundOrdinaryArchive.OAI.Paper320.Tournament.toDigraph
            (@OfNat.ofNat.{0} Nat (nat_lit 5591) (instOfNatNat (nat_lit 5591))) T)
          v w)
        (Adj v w))
  (hLabel :
    ∀ (v w : Fin (@OfNat.ofNat.{0} Nat (nat_lit 5591) (instOfNatNat (nat_lit 5591)))),
      @Eq.{1} Bool
        (@DFunLike.coe.{1, 1, 1} (Equiv.{1, 1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Bool)
          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (fun (x : Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) => Bool)
          (@EquivLike.toFunLike.{1, 1, 1}
            (Equiv.{1, 1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Bool)
            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Bool
            (@Equiv.instEquivLike.{1, 1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Bool))
          finTwoEquiv (ell v w))
        (label v w))
  (hCaps :
    @Sensitivity213981Formal.ThreeBoundOrdinary5591.LabelCaps
      (@OfNat.ofNat.{0} Nat (nat_lit 5591) (instOfNatNat (nat_lit 5591))) T ell)
  (p : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
  (F : Fin (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22))) → (I → Bool) → Bool)
  (hF :
    @Sensitivity213981Formal.ThreeBoundProfiles.Nested
      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22)))) I
      (@PartialOrder.toPreorder.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22))))
        (@Fin.instPartialOrder (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22)))))
      F)
  (v :
    Sensitivity213981Formal.ThreeBoundFullProfile.Profile
      (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22))))
  (hv :
    @Sensitivity213981Formal.ThreeBoundFullProfile.Upper (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22)))
      I inst F v)
  (i j : Fin (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22))))
  (hij :
    @LE.le.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22))))
      (@instLEFin (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22)))) i j)
  (hq4 :
    @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
      (Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Entry.tolerance
        (Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Endpoint22.recipe p j))),
  @Sensitivity213981Formal.ThreeBoundProfiles.ABound
    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22))))
    (Prod.{0, 0} (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5591) (instOfNatNat (nat_lit 5591)))) Bool) I)
    (@instFintypeProd.{0, 0}
      (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5591) (instOfNatNat (nat_lit 5591)))) Bool) I
      (@instFintypeProd.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5591) (instOfNatNat (nat_lit 5591)))) Bool
        (Fin.fintype (@OfNat.ofNat.{0} Nat (nat_lit 5591) (instOfNatNat (nat_lit 5591)))) Bool.fintype)
      inst)
    (@Sensitivity213981Formal.ThreeBoundWitness.parent
      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22)))) I
      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5591) (instOfNatNat (nat_lit 5591))))
      (Fin.fintype (@OfNat.ofNat.{0} Nat (nat_lit 5591) (instOfNatNat (nat_lit 5591))))
      (@Sensitivity213981Formal.ThreeBoundWitness.MinMaxRecipe.stage
        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22)))) I
        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5591) (instOfNatNat (nat_lit 5591))))
        (Sensitivity213981Formal.Sensitivity5591Endpoint22.recipe Adj loopless label p) F)
      F)
    i j
    (@Sensitivity213981Formal.ThreeBoundNumeric.Expr.eval
      (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22))) v
      (Sensitivity213981Formal.ThreeBoundNumeric.ordinaryAExpr
        (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22)))
        Sensitivity213981Formal.ThreeBoundOrdinary5591.numericCaps
        (Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Entry.lowerAt
          (Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Endpoint22.recipe p i)
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Entry.guard
          (Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Endpoint22.recipe p i))
        (Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Entry.tolerance
          (Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Endpoint22.recipe p i))
        (Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Entry.lowerAt
          (Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Endpoint22.recipe p j)
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Entry.guard
          (Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Endpoint22.recipe p j))
        (Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Entry.tolerance
          (Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Endpoint22.recipe p j)))) := by sorry
