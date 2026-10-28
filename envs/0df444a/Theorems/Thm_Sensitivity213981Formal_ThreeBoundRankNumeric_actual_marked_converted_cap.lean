-- Prove2me | Theorems.Thm_Sensitivity213981Formal_ThreeBoundRankNumeric_actual_marked_converted_cap
-- name    : Sensitivity213981Formal.ThreeBoundRankNumeric.actual_marked_converted_cap
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T01:34:12.668737+00:00
-- url     : https://prove2.me/theorems/0c3db2ea-394b-4cac-9dc7-ac60b133c91f
-- title:
--   actual marked converted cap — Boolean sensitivity certificate
-- statement:
--   The following universally quantified assertion holds for the finite sets, Boolean families, tournament data, and profile coordinates defined in the imported interfaces. Each binder specifies the domain of its variable, and bracketed conditions specify finite or ordered structures.
--
--   $$
--   \forall n:\mathbb N,\quad \forall I:\mathcal U,\quad \forall V:\mathcal U,\quad \bigl[\mathrm{finite}(I)\bigr]\;\bigl[\mathrm{finite}(V)\bigr]\;\forall S:\operatorname{Witness.Stage}\bigl(\{0,\ldots,n-1\}, I, V\bigr),\quad \bigl(\operatorname{TournamentHighRows.IsTournament}\bigl(\operatorname{Stage.Adj}\bigl(S\bigr)\bigr)\Longrightarrow \forall F:\left(\{0,\ldots,n-1\}\to \left(\left(I\to \mathbb B\right)\to \mathbb B\right)\right),\quad \bigl(\operatorname{Profiles.Nested}\bigl(F\bigr)\Longrightarrow \forall i:\{0,\ldots,n-1\},\quad \forall j:\{0,\ldots,n-1\},\quad \forall P:\operatorname{MinmaxTransfer.PairData}\bigl(S, F, i, j\bigr),\quad \forall x:\left(V\times \mathbb B\times I\to \mathbb B\right),\quad \forall q:\mathbb N,\quad \forall m:\mathbb N,\quad \forall a:\mathbb N,\quad \bigl(\bigl(m \le |\operatorname{MinmaxCandidates.guardSources}\bigl(S, F, \operatorname{PairData.strongLower}\bigl(P\bigr), \operatorname{PairData.strongUpper}\bigl(P\bigr), j, x\bigr)|\bigr)\Longrightarrow \bigl(\bigl(\bigl(m \le \bigl(q+2\bigr)\bigr) \lor \bigl(\operatorname{Stage.tolerance}\bigl(S, j\bigr) \le q\bigr)\bigr)\Longrightarrow \bigl(\operatorname{ResidualCaps.MarkedCardBound}\bigl(\operatorname{Stage.Adj}\bigl(S\bigr), \operatorname{Stage.label}\bigl(S\bigr), q, m, 0, a\bigr)\Longrightarrow \bigl(|\operatorname{RankNumeric.negativePrefix}\bigl(S, F, \operatorname{PairData.strongLower}\bigl(P\bigr), \operatorname{PairData.strongUpper}\bigl(P\bigr), j, x, q\bigr)| \le \bigl(\bigl(a-1\bigr)+\operatorname{RankNumeric.allowance}\bigl(m, \operatorname{RankNumeric.convertedCount}\bigl(S, F, \operatorname{PairData.strongLower}\bigl(P\bigr), \operatorname{PairData.strongUpper}\bigl(P\bigr), j, x\bigr), |\operatorname{MinmaxCandidates.guardSources}\bigl(S, F, \operatorname{PairData.strongLower}\bigl(P\bigr), \operatorname{PairData.strongUpper}\bigl(P\bigr), j, x\bigr)|\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)
--   $$
--
--   Here $\mathbb B=\{\mathsf{false},\mathsf{true}\}$; $\mathcal P_{\mathrm{fin}}(X)$ denotes the finite subsets of $X$. Named functions and predicates refer to their definitions in the cited source. This result supplies the corresponding actual marked converted cap step in the verified $22$-level sensitivity construction.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; RankConvertedCaps.lean, lines 150–175.

import Definitions.Def_Sensitivity213981Formal_GlobalAccounting
import Definitions.Def_Sensitivity213981Formal_GradedCandidates
import Definitions.Def_Sensitivity213981Formal_GuardAugmentation
import Definitions.Def_Sensitivity213981Formal_MinmaxCandidates
import Definitions.Def_Sensitivity213981Formal_MinmaxPairData
import Definitions.Def_Sensitivity213981Formal_MinmaxPrefixCaps
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_Q2EnumerationBridge
import Definitions.Def_Sensitivity213981Formal_RankConvertedCaps
import Definitions.Def_Sensitivity213981Formal_ResidualCaps
import Definitions.Def_Sensitivity213981Formal_Supplement_CandidateCoherence
import Definitions.Def_Sensitivity213981Formal_TournamentHighRows
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
import Mathlib.Algebra.Order.BigOperators.Group.List
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

theorem Sensitivity213981Formal.ThreeBoundRankNumeric.actual_marked_converted_cap :
∀ {n : Nat} {I V : Type} [Fintype.{0} I] [inst : Fintype.{0} V]
  (S : Sensitivity213981Formal.ThreeBoundWitness.Stage (Fin n) I V)
  (hR :
    @Sensitivity213981Formal.TournamentHighRows.IsTournament V
      (@Sensitivity213981Formal.ThreeBoundWitness.Stage.Adj (Fin n) I V S))
  (F : Fin n → (I → Bool) → Bool)
  (hF :
    @Sensitivity213981Formal.ThreeBoundProfiles.Nested (Fin n) I
      (@PartialOrder.toPreorder.{0} (Fin n) (@Fin.instPartialOrder n)) F)
  (i j : Fin n)
  (P :
    @Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData (Fin n) I V
      (@PartialOrder.toPreorder.{0} (Fin n) (@Fin.instPartialOrder n)) S F i j)
  (x : Prod.{0, 0} (Prod.{0, 0} V Bool) I → Bool) (q m a : Nat)
  (hm :
    @LE.le.{0} Nat instLENat m
      (@Finset.card.{0} V
        (@Sensitivity213981Formal.ThreeBoundMinmaxCandidates.guardSources (Fin n) I V inst S F
          (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower (Fin n) I V
            (@PartialOrder.toPreorder.{0} (Fin n) (@Fin.instPartialOrder n)) S F i j P)
          (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper (Fin n) I V
            (@PartialOrder.toPreorder.{0} (Fin n) (@Fin.instPartialOrder n)) S F i j P)
          j x)))
  (hbudget :
    Or
      (@LE.le.{0} Nat instLENat m
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) q
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@LE.le.{0} Nat instLENat (@Sensitivity213981Formal.ThreeBoundWitness.Stage.tolerance (Fin n) I V S j) q))
  (hcap :
    @Sensitivity213981Formal.ResidualCaps.MarkedCardBound V
      (@Sensitivity213981Formal.ThreeBoundWitness.Stage.Adj (Fin n) I V S)
      (@Sensitivity213981Formal.ThreeBoundWitness.Stage.label (Fin n) I V S) q m
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) a),
  @LE.le.{0} Nat instLENat
    (@Finset.card.{0} V
      (@Sensitivity213981Formal.ThreeBoundRankNumeric.negativePrefix n I V inst S F
        (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower (Fin n) I V
          (@PartialOrder.toPreorder.{0} (Fin n) (@Fin.instPartialOrder n)) S F i j P)
        (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper (Fin n) I V
          (@PartialOrder.toPreorder.{0} (Fin n) (@Fin.instPartialOrder n)) S F i j P)
        j x q))
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) a
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (Sensitivity213981Formal.ThreeBoundRankNumeric.allowance m
        (@Sensitivity213981Formal.ThreeBoundRankNumeric.convertedCount n I V inst S F
          (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower (Fin n) I V
            (@PartialOrder.toPreorder.{0} (Fin n) (@Fin.instPartialOrder n)) S F i j P)
          (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper (Fin n) I V
            (@PartialOrder.toPreorder.{0} (Fin n) (@Fin.instPartialOrder n)) S F i j P)
          j x)
        (@Finset.card.{0} V
          (@Sensitivity213981Formal.ThreeBoundMinmaxCandidates.guardSources (Fin n) I V inst S F
            (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower (Fin n) I V
              (@PartialOrder.toPreorder.{0} (Fin n) (@Fin.instPartialOrder n)) S F i j P)
            (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper (Fin n) I V
              (@PartialOrder.toPreorder.{0} (Fin n) (@Fin.instPartialOrder n)) S F i j P)
            j x)))) := by sorry
