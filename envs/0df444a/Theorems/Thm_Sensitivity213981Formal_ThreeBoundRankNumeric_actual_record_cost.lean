-- Prove2me | Theorems.Thm_Sensitivity213981Formal_ThreeBoundRankNumeric_actual_record_cost
-- name    : Sensitivity213981Formal.ThreeBoundRankNumeric.actual_record_cost
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T01:52:13.04744+00:00
-- url     : https://prove2.me/theorems/4d63de17-30b6-43b8-b35e-1134abf4f3cd
-- title:
--   actual record cost — Boolean sensitivity certificate
-- statement:
--   The following universally quantified assertion holds for the finite sets, Boolean families, tournament data, and profile coordinates defined in the imported interfaces. Each binder specifies the domain of its variable, and bracketed conditions specify finite or ordered structures.
--
--   $$
--   \forall n:\mathbb N,\quad \forall I:\mathcal U,\quad \forall V:\mathcal U,\quad \bigl[\mathrm{finite}(I)\bigr]\;\bigl[\mathrm{finite}(V)\bigr]\;\forall S:\operatorname{Witness.Stage}\bigl(\{0,\ldots,n-1\}, I, V\bigr),\quad \bigl(\operatorname{TournamentHighRows.IsTournament}\bigl(\operatorname{Stage.Adj}\bigl(S\bigr)\bigr)\Longrightarrow \forall F:\left(\{0,\ldots,n-1\}\to \left(\left(I\to \mathbb B\right)\to \mathbb B\right)\right),\quad \bigl(\operatorname{Profiles.Nested}\bigl(F\bigr)\Longrightarrow \forall i:\{0,\ldots,n-1\},\quad \forall j:\{0,\ldots,n-1\},\quad \forall P:\operatorname{MinmaxTransfer.PairData}\bigl(S, F, i, j\bigr),\quad \forall a:\operatorname{RankNumeric.Entry},\quad \forall c:\operatorname{RankNumeric.Entry},\quad \bigl(\operatorname{MinmaxNumeric.EntryMatch}\bigl(S, F, i, j, P, a, c\bigr)\Longrightarrow \forall \mathit{input}:\left(V\times \mathbb B\times I\to \mathbb B\right),\quad \bigl(\bigl(\operatorname{Witness.parent}\bigl(S, F, i, \mathit{input}\bigr) = \mathsf{false}\bigr)\Longrightarrow \bigl(\bigl(\operatorname{Stage.tolerance}\bigl(S, j\bigr) \le 3\bigr)\Longrightarrow \forall \mathit{caps}:\operatorname{Numeric.Caps},\quad \forall \mathit{perfect}:\mathbb N,\quad \bigl(\operatorname{RankNumeric.CapsSound}\bigl(\operatorname{Stage.Adj}\bigl(S\bigr), \operatorname{Stage.label}\bigl(S\bigr), \mathit{caps}, \mathit{perfect}\bigr)\Longrightarrow \forall v:\operatorname{FullProfile.Profile}\bigl(n\bigr),\quad \bigl(\operatorname{FullProfile.Upper}\bigl(F, v\bigr)\Longrightarrow \bigl(\operatorname{Numeric.Ordered}\bigl(v\bigr)\Longrightarrow \exists \mathit{xs}:\operatorname{List}(\mathbb N),\quad \bigl(\mathit{xs}\in \operatorname{Q3.records} \land \exists e:\mathbb N,\quad \bigl(\bigl(e \le \operatorname{Numeric.recordOfList}\bigl(\mathit{xs}, 11\bigr)\bigr) \land \bigl(\bigl(\operatorname{RankNumeric.recordAllowed}\bigl(n, \mathit{caps}, a, c, \operatorname{Numeric.recordOfList}\bigl(\mathit{xs}\bigr)\bigr) = \mathsf{true}\bigr) \land \bigl(|\operatorname{Profiles.flipsTo}\bigl(\operatorname{Witness.parent}\bigl(S, F, j\bigr), \mathsf{true}, \mathit{input}\bigr)| \le \operatorname{Expr.eval}\bigl(v, \operatorname{RankNumeric.recordCost}\bigl(n, \mathit{caps}, \mathit{perfect}, a, c, \operatorname{Numeric.recordOfList}\bigl(\mathit{xs}\bigr), e\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)
--   $$
--
--   Here $\mathbb B=\{\mathsf{false},\mathsf{true}\}$; $\mathcal P_{\mathrm{fin}}(X)$ denotes the finite subsets of $X$. Named functions and predicates refer to their definitions in the cited source. This result supplies the corresponding actual record cost step in the verified $22$-level sensitivity construction.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; RankABound.lean, lines 37–113.

import Definitions.Def_Sensitivity213981Formal_GlobalAccounting
import Definitions.Def_Sensitivity213981Formal_GradedCandidates
import Definitions.Def_Sensitivity213981Formal_HeadCostExpressions
import Definitions.Def_Sensitivity213981Formal_MinmaxCandidates
import Definitions.Def_Sensitivity213981Formal_MinmaxNegative
import Definitions.Def_Sensitivity213981Formal_MinmaxPairData
import Definitions.Def_Sensitivity213981Formal_MinmaxPrefixCaps
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_Q2EnumerationBridge
import Definitions.Def_Sensitivity213981Formal_Q2RawExpressions
import Definitions.Def_Sensitivity213981Formal_Q3Enumeration
import Definitions.Def_Sensitivity213981Formal_Q3RecordFields
import Definitions.Def_Sensitivity213981Formal_RankCapData
import Definitions.Def_Sensitivity213981Formal_RankConvertedCaps
import Definitions.Def_Sensitivity213981Formal_RankCostExpressions
import Definitions.Def_Sensitivity213981Formal_ResidualCaps
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

theorem Sensitivity213981Formal.ThreeBoundRankNumeric.actual_record_cost :
∀ {n : Nat} {I V : Type} [inst : Fintype.{0} I] [inst_1 : Fintype.{0} V]
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
  (a c : Sensitivity213981Formal.ThreeBoundRankNumeric.Entry)
  (matchE : @Sensitivity213981Formal.ThreeBoundMinmaxNumeric.EntryMatch n I V S F i j P a c)
  (input : Prod.{0, 0} (Prod.{0, 0} V Bool) I → Bool)
  (hoff : @Eq.{1} Bool (@Sensitivity213981Formal.ThreeBoundWitness.parent (Fin n) I V inst_1 S F i input) Bool.false)
  (hQ :
    @LE.le.{0} Nat instLENat (@Sensitivity213981Formal.ThreeBoundWitness.Stage.tolerance (Fin n) I V S j)
      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
  (caps : Sensitivity213981Formal.ThreeBoundNumeric.Caps) (perfect : Nat)
  (hcaps :
    @Sensitivity213981Formal.ThreeBoundRankNumeric.CapsSound V inst_1
      (fun (a b : V) => Classical.propDecidable (@Eq.{1} V a b))
      (@Sensitivity213981Formal.ThreeBoundWitness.Stage.Adj (Fin n) I V S)
      (@Sensitivity213981Formal.ThreeBoundWitness.Stage.label (Fin n) I V S) caps perfect)
  (v : Sensitivity213981Formal.ThreeBoundFullProfile.Profile n)
  (hv : @Sensitivity213981Formal.ThreeBoundFullProfile.Upper n I inst F v)
  (hordered : @Sensitivity213981Formal.ThreeBoundNumeric.Ordered n v),
  @Exists.{1} (List.{0} Nat) fun (xs : List.{0} Nat) =>
    And
      (@Membership.mem.{0, 0} (List.{0} Nat) (List.{0} (List.{0} Nat)) (@List.instMembership.{0} (List.{0} Nat))
        Sensitivity213981Formal.ThreeBoundQ3.records xs)
      (@Exists.{1} Nat fun (e : Nat) =>
        And
          (@LE.le.{0} Nat instLENat e
            (Sensitivity213981Formal.ThreeBoundNumeric.recordOfList xs
              (@OfNat.ofNat.{0} Nat (nat_lit 11) (instOfNatNat (nat_lit 11)))))
          (And
            (@Eq.{1} Bool
              (Sensitivity213981Formal.ThreeBoundRankNumeric.recordAllowed n caps a c
                (Sensitivity213981Formal.ThreeBoundNumeric.recordOfList xs))
              Bool.true)
            (@LE.le.{0} Nat instLENat
              (@Finset.card.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I)
                (@Sensitivity213981Formal.ThreeBoundProfiles.flipsTo (Prod.{0, 0} (Prod.{0, 0} V Bool) I)
                  (@instFintypeProd.{0, 0} (Prod.{0, 0} V Bool) I (@instFintypeProd.{0, 0} V Bool inst_1 Bool.fintype)
                    inst)
                  (@Sensitivity213981Formal.ThreeBoundWitness.parent (Fin n) I V inst_1 S F j) Bool.true input))
              (@Sensitivity213981Formal.ThreeBoundNumeric.Expr.eval n v
                (Sensitivity213981Formal.ThreeBoundRankNumeric.recordCost n caps perfect a c
                  (Sensitivity213981Formal.ThreeBoundNumeric.recordOfList xs) e))))) := by sorry
