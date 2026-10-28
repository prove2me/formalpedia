-- Prove2me | Theorems.Thm_Sensitivity213981Formal_ThreeBoundRankNumeric_actual_external_split_bound
-- name    : Sensitivity213981Formal.ThreeBoundRankNumeric.actual_external_split_bound
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T01:33:20.919494+00:00
-- url     : https://prove2.me/theorems/b134a4fd-0856-42e2-9dad-f2822053463c
-- title:
--   actual external split bound — Boolean sensitivity certificate
-- statement:
--   The following universally quantified assertion holds for the finite sets, Boolean families, tournament data, and profile coordinates defined in the imported interfaces. Each binder specifies the domain of its variable, and bracketed conditions specify finite or ordered structures.
--
--   $$
--   \prod_{n:\mathbb N} \prod_{I:\mathcal U} \prod_{V:\mathcal U} \prod_{\mathit{inst}:\mathrm{finite}(I)} \prod_{\mathit{inst}:\mathrm{finite}(V)} \prod_{S:\operatorname{Witness.Stage}\bigl(\{0,\ldots,n-1\}, I, V\bigr)} \prod_{F:\left(\{0,\ldots,n-1\}\to \left(\left(I\to \mathbb B\right)\to \mathbb B\right)\right)} \prod_{\mathit{hF}:\operatorname{Profiles.Nested}\bigl(F\bigr)} \prod_{i:\{0,\ldots,n-1\}} \prod_{j:\{0,\ldots,n-1\}} \prod_{P:\operatorname{MinmaxTransfer.PairData}\bigl(S, F, i, j\bigr)} \prod_{a:\operatorname{RankNumeric.Entry}} \prod_{c:\operatorname{RankNumeric.Entry}} \left(\operatorname{MinmaxNumeric.EntryMatch}\bigl(S, F, i, j, P, a, c\bigr)\to \prod_{v:\operatorname{FullProfile.Profile}\bigl(n\bigr)} \prod_{\mathit{hv}:\operatorname{FullProfile.Upper}\bigl(F, v\bigr)} \prod_{x:\left(V\times \mathbb B\times I\to \mathbb B\right)} \prod_{\mathit{hoff}:\bigl(\operatorname{Witness.parent}\bigl(S, F, i, x\bigr) = \mathsf{false}\bigr)} \left(\text{let }\mathit{total}=\sum_{w\in \operatorname{MinmaxCandidates.guardSources}\bigl(S, F, \operatorname{PairData.strongLower}\bigl(P\bigr), \operatorname{PairData.strongUpper}\bigl(P\bigr), j, x\bigr)} \bigl(|\operatorname{Witness.failed}\bigl(S, F, j, x, w\bigr)|-|\operatorname{Finset.filter}\bigl(\operatorname{Stage.Adj}\bigl(S, w\bigr), \operatorname{MinmaxCandidates.highHeads}\bigl(S, F, \operatorname{PairData.strongLower}\bigl(P\bigr), \operatorname{PairData.strongUpper}\bigl(P\bigr), j, x\bigr)\bigr)|\bigr)\text{ in }\left(\text{let }e=\operatorname{RankNumeric.convertedCount}\bigl(S, F, \operatorname{PairData.strongLower}\bigl(P\bigr), \operatorname{PairData.strongUpper}\bigl(P\bigr), j, x\bigr)\text{ in }\bigl(|\operatorname{MinmaxCover.externalBits}\bigl(S, F, \operatorname{PairData.strongLower}\bigl(P\bigr), \operatorname{PairData.strongUpper}\bigl(P\bigr), j, x\bigr)| \le \bigl(\bigl(e\cdot \operatorname{Expr.eval}\bigl(v, \operatorname{Numeric.bExpr}\bigl(n, \operatorname{Entry.guard}\bigl(c\bigr), \operatorname{Entry.lowerAt}\bigl(c, 0\bigr)\bigr)\bigr)\bigr)+\bigl(\bigl(\mathit{total}-e\bigr)\cdot \operatorname{Expr.eval}\bigl(v, \operatorname{Numeric.bExpr}\bigl(n, \operatorname{Entry.guard}\bigl(c\bigr), \operatorname{Entry.guard}\bigl(a\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\right)\right)\right)
--   $$
--
--   Here $\mathbb B=\{\mathsf{false},\mathsf{true}\}$; $\mathcal P_{\mathrm{fin}}(X)$ denotes the finite subsets of $X$. Named functions and predicates refer to their definitions in the cited source. This result supplies the corresponding actual external split bound step in the verified $22$-level sensitivity construction.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; RankExternalSplit.lean, lines 102–131.

import Definitions.Def_Sensitivity213981Formal_GlobalAccounting
import Definitions.Def_Sensitivity213981Formal_MinmaxCandidates
import Definitions.Def_Sensitivity213981Formal_MinmaxPairData
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_RankExternalSplit
import Definitions.Def_Sensitivity213981Formal_Supplement_GradedPositiveBoundary
import Definitions.Def_Sensitivity213981Formal_Supplement_NumericExpressions
import Definitions.Def_Sensitivity213981Formal_WitnessLifting
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
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
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Sort
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Prod.Lex
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

theorem Sensitivity213981Formal.ThreeBoundRankNumeric.actual_external_split_bound :
∀ {n : Nat} {I V : Type} [inst : Fintype.{0} I] [inst_1 : Fintype.{0} V]
  (S : Sensitivity213981Formal.ThreeBoundWitness.Stage (Fin n) I V) (F : Fin n → (I → Bool) → Bool)
  (hF :
    @Sensitivity213981Formal.ThreeBoundProfiles.Nested (Fin n) I
      (@PartialOrder.toPreorder.{0} (Fin n) (@Fin.instPartialOrder n)) F)
  (i j : Fin n)
  (P :
    @Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData (Fin n) I V
      (@PartialOrder.toPreorder.{0} (Fin n) (@Fin.instPartialOrder n)) S F i j)
  (a c : Sensitivity213981Formal.ThreeBoundRankNumeric.Entry)
  (hm : @Sensitivity213981Formal.ThreeBoundMinmaxNumeric.EntryMatch n I V S F i j P a c)
  (v : Sensitivity213981Formal.ThreeBoundFullProfile.Profile n)
  (hv : @Sensitivity213981Formal.ThreeBoundFullProfile.Upper n I inst F v)
  (x : Prod.{0, 0} (Prod.{0, 0} V Bool) I → Bool)
  (hoff : @Eq.{1} Bool (@Sensitivity213981Formal.ThreeBoundWitness.parent (Fin n) I V inst_1 S F i x) Bool.false),
  have total : Nat :=
    @Finset.sum.{0, 0} V Nat Nat.instAddCommMonoid
      (@Sensitivity213981Formal.ThreeBoundMinmaxCandidates.guardSources (Fin n) I V inst_1 S F
        (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower (Fin n) I V
          (@PartialOrder.toPreorder.{0} (Fin n) (@Fin.instPartialOrder n)) S F i j P)
        (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper (Fin n) I V
          (@PartialOrder.toPreorder.{0} (Fin n) (@Fin.instPartialOrder n)) S F i j P)
        j x)
      fun (w : V) =>
      @HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
        (@Finset.card.{0} V (@Sensitivity213981Formal.ThreeBoundWitness.failed (Fin n) I V inst_1 S F j x w))
        (@Finset.card.{0} V
          (@Finset.filter.{0} V (@Sensitivity213981Formal.ThreeBoundWitness.Stage.Adj (Fin n) I V S w)
            (fun (a : V) =>
              Classical.propDecidable (@Sensitivity213981Formal.ThreeBoundWitness.Stage.Adj (Fin n) I V S w a))
            (@Sensitivity213981Formal.ThreeBoundMinmaxCandidates.highHeads (Fin n) I V inst_1 S F
              (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower (Fin n) I V
                (@PartialOrder.toPreorder.{0} (Fin n) (@Fin.instPartialOrder n)) S F i j P)
              (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper (Fin n) I V
                (@PartialOrder.toPreorder.{0} (Fin n) (@Fin.instPartialOrder n)) S F i j P)
              j x)));
  have e : Nat :=
    @Sensitivity213981Formal.ThreeBoundRankNumeric.convertedCount n I V inst_1 S F
      (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower (Fin n) I V
        (@PartialOrder.toPreorder.{0} (Fin n) (@Fin.instPartialOrder n)) S F i j P)
      (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper (Fin n) I V
        (@PartialOrder.toPreorder.{0} (Fin n) (@Fin.instPartialOrder n)) S F i j P)
      j x;
  @LE.le.{0} Nat instLENat
    (@Finset.card.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I)
      (@Sensitivity213981Formal.ThreeBoundMinmaxCover.externalBits (Fin n) I V inst inst_1 S F
        (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower (Fin n) I V
          (@PartialOrder.toPreorder.{0} (Fin n) (@Fin.instPartialOrder n)) S F i j P)
        (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper (Fin n) I V
          (@PartialOrder.toPreorder.{0} (Fin n) (@Fin.instPartialOrder n)) S F i j P)
        j x))
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) e
        (@Sensitivity213981Formal.ThreeBoundNumeric.Expr.eval n v
          (Sensitivity213981Formal.ThreeBoundNumeric.bExpr n
            (Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Entry.guard c)
            (Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Entry.lowerAt c
              (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) total e)
        (@Sensitivity213981Formal.ThreeBoundNumeric.Expr.eval n v
          (Sensitivity213981Formal.ThreeBoundNumeric.bExpr n
            (Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Entry.guard c)
            (Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Entry.guard a))))) := by sorry
