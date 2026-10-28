-- Prove2me | Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxQ3_actual_record_exists
-- name    : Sensitivity213981Formal.ThreeBoundMinmaxQ3.actual_record_exists
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T01:33:02.237474+00:00
-- url     : https://prove2.me/theorems/357541da-6c8e-436a-a671-856b74b6df45
-- title:
--   actual record exists — Boolean sensitivity certificate
-- statement:
--   The following universally quantified assertion holds for the finite sets, Boolean families, tournament data, and profile coordinates defined in the imported interfaces. Each binder specifies the domain of its variable, and bracketed conditions specify finite or ordered structures.
--
--   $$
--   \forall L:\mathcal U,\quad \forall I:\mathcal U,\quad \forall V:\mathcal U,\quad \bigl[\operatorname{LinearOrder}\bigl(L\bigr)\bigr]\;\bigl[\mathrm{finite}(I)\bigr]\;\bigl[\mathrm{finite}(V)\bigr]\;\forall S:\operatorname{Witness.Stage}\bigl(L, I, V\bigr),\quad \bigl(\operatorname{TournamentHighRows.IsTournament}\bigl(\operatorname{Stage.Adj}\bigl(S\bigr)\bigr)\Longrightarrow \forall F:\left(L\to \left(\left(I\to \mathbb B\right)\to \mathbb B\right)\right),\quad \bigl(\operatorname{Profiles.Nested}\bigl(F\bigr)\Longrightarrow \forall i:L,\quad \forall j:L,\quad \forall P:\operatorname{MinmaxTransfer.PairData}\bigl(S, F, i, j\bigr),\quad \forall x:\left(V\times \mathbb B\times I\to \mathbb B\right),\quad \bigl(\bigl(\operatorname{Stage.tolerance}\bigl(S, j\bigr) \le 3\bigr)\Longrightarrow \forall \mathit{tag}:\left(V\to \operatorname{Q3.Kind}\right),\quad \bigl(\forall w:V,\quad \bigl(w\in \operatorname{MinmaxCandidates.highHeads}\bigl(S, F, \operatorname{PairData.strongLower}\bigl(P\bigr), \operatorname{PairData.strongUpper}\bigl(P\bigr), j, x\bigr)\Longrightarrow \operatorname{HighTypes.OfKind}\bigl(3, \operatorname{MinmaxCandidates.PositiveCandidate}\bigl(S, F, \operatorname{PairData.strongLower}\bigl(P\bigr), \operatorname{PairData.strongUpper}\bigl(P\bigr), j, x, w\bigr), \operatorname{MinmaxCandidates.GuardCandidate}\bigl(S, F, \operatorname{PairData.strongLower}\bigl(P\bigr), \operatorname{PairData.strongUpper}\bigl(P\bigr), j, x, w\bigr), \mathit{tag}\bigl(w\bigr)\bigr)\bigr)\Longrightarrow \bigl(\forall v:V,\quad \bigl(v\in \operatorname{MinmaxCandidates.highHeads}\bigl(S, F, \operatorname{PairData.strongLower}\bigl(P\bigr), \operatorname{PairData.strongUpper}\bigl(P\bigr), j, x\bigr)\Longrightarrow \bigl(|\operatorname{Finset.filter}\bigl(\operatorname{Stage.Adj}\bigl(S, v\bigr), \operatorname{MinmaxCandidates.highHeads}\bigl(S, F, \operatorname{PairData.strongLower}\bigl(P\bigr), \operatorname{PairData.strongUpper}\bigl(P\bigr), j, x\bigr)\bigr)| \le \operatorname{Q3.budget}\bigl(\mathit{tag}\bigl(v\bigr)\bigr)\bigr)\bigr)\Longrightarrow \exists \mathit{ts}:\operatorname{List}(\operatorname{Q3.Kind}),\quad \exists \mathit{ds}:\operatorname{List}(\mathbb B),\quad \exists e:\operatorname{Equiv}\bigl(\{0,\ldots,|\mathit{ts}|-1\}, \operatorname{Subtype}\bigl(\left(x\mapsto x\in \operatorname{MinmaxCandidates.highHeads}\bigl(S, F, \operatorname{PairData.strongLower}\bigl(P\bigr), \operatorname{PairData.strongUpper}\bigl(P\bigr), j, x\bigr)\right)\bigr)\bigr),\quad \bigl(\operatorname{List.Pairwise}\bigl(\left(a\mapsto \left(b\mapsto \bigl(\operatorname{Q3.orderKey}\bigl(a\bigr) \le \operatorname{Q3.orderKey}\bigl(b\bigr)\bigr)\right)\right), \mathit{ts}\bigr) \land \bigl(\forall k:\{0,\ldots,|\mathit{ts}|-1\},\quad \bigl(\operatorname{List.get}\bigl(\mathit{ts}, k\bigr) = \mathit{tag}\bigl(\operatorname{DFunLike.coe}\bigl(e, k\bigr)\bigr)\bigr) \land \bigl(\bigl(\mathit{ds} = \operatorname{Q2.orientationBits}\bigl(\left(k\mapsto \left(l\mapsto \operatorname{Stage.Adj}\bigl(S, \operatorname{DFunLike.coe}\bigl(e, k\bigr), \operatorname{DFunLike.coe}\bigl(e, l\bigr)\bigr)\right)\right)\bigr)\bigr) \land \operatorname{Q3.record}\bigl((\mathit{ts},\mathit{ds})\bigr)\in \operatorname{Q3.records}\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)
--   $$
--
--   Here $\mathbb B=\{\mathsf{false},\mathsf{true}\}$; $\mathcal P_{\mathrm{fin}}(X)$ denotes the finite subsets of $X$. Named functions and predicates refer to their definitions in the cited source. This result supplies the corresponding actual record exists step in the verified $22$-level sensitivity construction.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Q3ActualEnumeration.lean, lines 17–74.

import Definitions.Def_Sensitivity213981Formal_GlobalAccounting
import Definitions.Def_Sensitivity213981Formal_GradedCandidates
import Definitions.Def_Sensitivity213981Formal_HighTypeCore
import Definitions.Def_Sensitivity213981Formal_MinmaxCandidates
import Definitions.Def_Sensitivity213981Formal_MinmaxPairData
import Definitions.Def_Sensitivity213981Formal_MinmaxPrefixCaps
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_Q2EnumerationBridge
import Definitions.Def_Sensitivity213981Formal_Q3Enumeration
import Definitions.Def_Sensitivity213981Formal_RankCapData
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

theorem Sensitivity213981Formal.ThreeBoundMinmaxQ3.actual_record_exists :
∀ {L I V : Type} [inst : LinearOrder.{0} L] [Fintype.{0} I] [inst_2 : Fintype.{0} V]
  (S : Sensitivity213981Formal.ThreeBoundWitness.Stage L I V)
  (hR :
    @Sensitivity213981Formal.TournamentHighRows.IsTournament V
      (@Sensitivity213981Formal.ThreeBoundWitness.Stage.Adj L I V S))
  (F : L → (I → Bool) → Bool)
  (hF :
    @Sensitivity213981Formal.ThreeBoundProfiles.Nested L I
      (@PartialOrder.toPreorder.{0} L
        (@SemilatticeInf.toPartialOrder.{0} L
          (@Lattice.toSemilatticeInf.{0} L
            (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
      F)
  (i j : L)
  (P :
    @Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData L I V
      (@PartialOrder.toPreorder.{0} L
        (@SemilatticeInf.toPartialOrder.{0} L
          (@Lattice.toSemilatticeInf.{0} L
            (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
      S F i j)
  (x : Prod.{0, 0} (Prod.{0, 0} V Bool) I → Bool)
  (hQ :
    @LE.le.{0} Nat instLENat (@Sensitivity213981Formal.ThreeBoundWitness.Stage.tolerance L I V S j)
      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
  (tag : V → Sensitivity213981Formal.ThreeBoundQ3.Kind)
  (hk :
    ∀ (w : V),
      @Membership.mem.{0, 0} V (Finset.{0} V)
          (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V))
          (@Sensitivity213981Formal.ThreeBoundMinmaxCandidates.highHeads L I V inst_2 S F
            (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower L I V
              (@PartialOrder.toPreorder.{0} L
                (@SemilatticeInf.toPartialOrder.{0} L
                  (@Lattice.toSemilatticeInf.{0} L
                    (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
              S F i j P)
            (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper L I V
              (@PartialOrder.toPreorder.{0} L
                (@SemilatticeInf.toPartialOrder.{0} L
                  (@Lattice.toSemilatticeInf.{0} L
                    (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
              S F i j P)
            j x)
          w →
        Sensitivity213981Formal.ThreeBoundHighTypes.OfKind (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
          (@Sensitivity213981Formal.ThreeBoundMinmaxCandidates.PositiveCandidate L I V inst_2 S F
            (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower L I V
              (@PartialOrder.toPreorder.{0} L
                (@SemilatticeInf.toPartialOrder.{0} L
                  (@Lattice.toSemilatticeInf.{0} L
                    (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
              S F i j P)
            (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper L I V
              (@PartialOrder.toPreorder.{0} L
                (@SemilatticeInf.toPartialOrder.{0} L
                  (@Lattice.toSemilatticeInf.{0} L
                    (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
              S F i j P)
            j x w)
          (@Sensitivity213981Formal.ThreeBoundMinmaxCandidates.GuardCandidate L I V inst_2 S F
            (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower L I V
              (@PartialOrder.toPreorder.{0} L
                (@SemilatticeInf.toPartialOrder.{0} L
                  (@Lattice.toSemilatticeInf.{0} L
                    (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
              S F i j P)
            (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper L I V
              (@PartialOrder.toPreorder.{0} L
                (@SemilatticeInf.toPartialOrder.{0} L
                  (@Lattice.toSemilatticeInf.{0} L
                    (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
              S F i j P)
            j x w)
          (tag w))
  (hout :
    ∀ (v : V),
      @Membership.mem.{0, 0} V (Finset.{0} V)
          (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V))
          (@Sensitivity213981Formal.ThreeBoundMinmaxCandidates.highHeads L I V inst_2 S F
            (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower L I V
              (@PartialOrder.toPreorder.{0} L
                (@SemilatticeInf.toPartialOrder.{0} L
                  (@Lattice.toSemilatticeInf.{0} L
                    (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
              S F i j P)
            (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper L I V
              (@PartialOrder.toPreorder.{0} L
                (@SemilatticeInf.toPartialOrder.{0} L
                  (@Lattice.toSemilatticeInf.{0} L
                    (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
              S F i j P)
            j x)
          v →
        @LE.le.{0} Nat instLENat
          (@Finset.card.{0} V
            (@Finset.filter.{0} V (@Sensitivity213981Formal.ThreeBoundWitness.Stage.Adj L I V S v)
              (fun (a : V) =>
                Classical.propDecidable (@Sensitivity213981Formal.ThreeBoundWitness.Stage.Adj L I V S v a))
              (@Sensitivity213981Formal.ThreeBoundMinmaxCandidates.highHeads L I V inst_2 S F
                (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower L I V
                  (@PartialOrder.toPreorder.{0} L
                    (@SemilatticeInf.toPartialOrder.{0} L
                      (@Lattice.toSemilatticeInf.{0} L
                        (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                  S F i j P)
                (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper L I V
                  (@PartialOrder.toPreorder.{0} L
                    (@SemilatticeInf.toPartialOrder.{0} L
                      (@Lattice.toSemilatticeInf.{0} L
                        (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                  S F i j P)
                j x)))
          (Sensitivity213981Formal.ThreeBoundQ3.budget (tag v))),
  @Exists.{1} (List.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind)
    fun (ts : List.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind) =>
    @Exists.{1} (List.{0} Bool) fun (ds : List.{0} Bool) =>
      @Exists.{1}
        (Equiv.{1, 1} (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts))
          (@Subtype.{1} V fun (x_1 : V) =>
            @Membership.mem.{0, 0} V (Finset.{0} V)
              (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V))
              (@Sensitivity213981Formal.ThreeBoundMinmaxCandidates.highHeads L I V inst_2 S F
                (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower L I V
                  (@PartialOrder.toPreorder.{0} L
                    (@SemilatticeInf.toPartialOrder.{0} L
                      (@Lattice.toSemilatticeInf.{0} L
                        (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                  S F i j P)
                (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper L I V
                  (@PartialOrder.toPreorder.{0} L
                    (@SemilatticeInf.toPartialOrder.{0} L
                      (@Lattice.toSemilatticeInf.{0} L
                        (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                  S F i j P)
                j x)
              x_1))
        fun
          (e :
            Equiv.{1, 1} (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts))
              (@Subtype.{1} V fun (x_1 : V) =>
                @Membership.mem.{0, 0} V (Finset.{0} V)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V))
                  (@Sensitivity213981Formal.ThreeBoundMinmaxCandidates.highHeads L I V inst_2 S F
                    (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower L I V
                      (@PartialOrder.toPreorder.{0} L
                        (@SemilatticeInf.toPartialOrder.{0} L
                          (@Lattice.toSemilatticeInf.{0} L
                            (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                      S F i j P)
                    (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper L I V
                      (@PartialOrder.toPreorder.{0} L
                        (@SemilatticeInf.toPartialOrder.{0} L
                          (@Lattice.toSemilatticeInf.{0} L
                            (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                      S F i j P)
                    j x)
                  x_1)) =>
        And
          (@List.Pairwise.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind
            (fun (a b : Sensitivity213981Formal.ThreeBoundQ3.Kind) =>
              @LE.le.{0} Nat instLENat (Sensitivity213981Formal.ThreeBoundQ3.orderKey a)
                (Sensitivity213981Formal.ThreeBoundQ3.orderKey b))
            ts)
          (And
            (∀ (k : Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts)),
              @Eq.{1} Sensitivity213981Formal.ThreeBoundQ3.Kind
                (@List.get.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts k)
                (tag
                  (@Subtype.val.{1} V
                    (fun (x_1 : V) =>
                      @Membership.mem.{0, 0} V (Finset.{0} V)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V))
                        (@Sensitivity213981Formal.ThreeBoundMinmaxCandidates.highHeads L I V inst_2 S F
                          (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower L I V
                            (@PartialOrder.toPreorder.{0} L
                              (@SemilatticeInf.toPartialOrder.{0} L
                                (@Lattice.toSemilatticeInf.{0} L
                                  (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                            S F i j P)
                          (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper L I V
                            (@PartialOrder.toPreorder.{0} L
                              (@SemilatticeInf.toPartialOrder.{0} L
                                (@Lattice.toSemilatticeInf.{0} L
                                  (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                            S F i j P)
                          j x)
                        x_1)
                    (@DFunLike.coe.{1, 1, 1}
                      (Equiv.{1, 1} (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts))
                        (@Subtype.{1} V fun (x_1 : V) =>
                          @Membership.mem.{0, 0} V (Finset.{0} V)
                            (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V))
                            (@Sensitivity213981Formal.ThreeBoundMinmaxCandidates.highHeads L I V inst_2 S F
                              (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower L I V
                                (@PartialOrder.toPreorder.{0} L
                                  (@SemilatticeInf.toPartialOrder.{0} L
                                    (@Lattice.toSemilatticeInf.{0} L
                                      (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                                S F i j P)
                              (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper L I V
                                (@PartialOrder.toPreorder.{0} L
                                  (@SemilatticeInf.toPartialOrder.{0} L
                                    (@Lattice.toSemilatticeInf.{0} L
                                      (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                                S F i j P)
                              j x)
                            x_1))
                      (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts))
                      (fun (x_1 : Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts)) =>
                        @Subtype.{1} V fun (x_2 : V) =>
                          @Membership.mem.{0, 0} V (Finset.{0} V)
                            (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V))
                            (@Sensitivity213981Formal.ThreeBoundMinmaxCandidates.highHeads L I V inst_2 S F
                              (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower L I V
                                (@PartialOrder.toPreorder.{0} L
                                  (@SemilatticeInf.toPartialOrder.{0} L
                                    (@Lattice.toSemilatticeInf.{0} L
                                      (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                                S F i j P)
                              (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper L I V
                                (@PartialOrder.toPreorder.{0} L
                                  (@SemilatticeInf.toPartialOrder.{0} L
                                    (@Lattice.toSemilatticeInf.{0} L
                                      (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                                S F i j P)
                              j x)
                            x_2)
                      (@EquivLike.toFunLike.{1, 1, 1}
                        (Equiv.{1, 1} (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts))
                          (@Subtype.{1} V fun (x_1 : V) =>
                            @Membership.mem.{0, 0} V (Finset.{0} V)
                              (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V))
                              (@Sensitivity213981Formal.ThreeBoundMinmaxCandidates.highHeads L I V inst_2 S F
                                (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower L I V
                                  (@PartialOrder.toPreorder.{0} L
                                    (@SemilatticeInf.toPartialOrder.{0} L
                                      (@Lattice.toSemilatticeInf.{0} L
                                        (@DistribLattice.toLattice.{0} L
                                          (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                                  S F i j P)
                                (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper L I V
                                  (@PartialOrder.toPreorder.{0} L
                                    (@SemilatticeInf.toPartialOrder.{0} L
                                      (@Lattice.toSemilatticeInf.{0} L
                                        (@DistribLattice.toLattice.{0} L
                                          (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                                  S F i j P)
                                j x)
                              x_1))
                        (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts))
                        (@Subtype.{1} V fun (x_1 : V) =>
                          @Membership.mem.{0, 0} V (Finset.{0} V)
                            (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V))
                            (@Sensitivity213981Formal.ThreeBoundMinmaxCandidates.highHeads L I V inst_2 S F
                              (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower L I V
                                (@PartialOrder.toPreorder.{0} L
                                  (@SemilatticeInf.toPartialOrder.{0} L
                                    (@Lattice.toSemilatticeInf.{0} L
                                      (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                                S F i j P)
                              (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper L I V
                                (@PartialOrder.toPreorder.{0} L
                                  (@SemilatticeInf.toPartialOrder.{0} L
                                    (@Lattice.toSemilatticeInf.{0} L
                                      (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                                S F i j P)
                              j x)
                            x_1)
                        (@Equiv.instEquivLike.{1, 1}
                          (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts))
                          (@Subtype.{1} V fun (x_1 : V) =>
                            @Membership.mem.{0, 0} V (Finset.{0} V)
                              (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V))
                              (@Sensitivity213981Formal.ThreeBoundMinmaxCandidates.highHeads L I V inst_2 S F
                                (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower L I V
                                  (@PartialOrder.toPreorder.{0} L
                                    (@SemilatticeInf.toPartialOrder.{0} L
                                      (@Lattice.toSemilatticeInf.{0} L
                                        (@DistribLattice.toLattice.{0} L
                                          (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                                  S F i j P)
                                (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper L I V
                                  (@PartialOrder.toPreorder.{0} L
                                    (@SemilatticeInf.toPartialOrder.{0} L
                                      (@Lattice.toSemilatticeInf.{0} L
                                        (@DistribLattice.toLattice.{0} L
                                          (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                                  S F i j P)
                                j x)
                              x_1)))
                      e k))))
            (And
              (@Eq.{1} (List.{0} Bool) ds
                (@Sensitivity213981Formal.ThreeBoundQ2.orientationBits
                  (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts)
                  (fun (k l : Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts)) =>
                    @Sensitivity213981Formal.ThreeBoundWitness.Stage.Adj L I V S
                      (@Subtype.val.{1} V
                        (fun (x_1 : V) =>
                          @Membership.mem.{0, 0} V (Finset.{0} V)
                            (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V))
                            (@Sensitivity213981Formal.ThreeBoundMinmaxCandidates.highHeads L I V inst_2 S F
                              (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower L I V
                                (@PartialOrder.toPreorder.{0} L
                                  (@SemilatticeInf.toPartialOrder.{0} L
                                    (@Lattice.toSemilatticeInf.{0} L
                                      (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                                S F i j P)
                              (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper L I V
                                (@PartialOrder.toPreorder.{0} L
                                  (@SemilatticeInf.toPartialOrder.{0} L
                                    (@Lattice.toSemilatticeInf.{0} L
                                      (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                                S F i j P)
                              j x)
                            x_1)
                        (@DFunLike.coe.{1, 1, 1}
                          (Equiv.{1, 1} (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts))
                            (@Subtype.{1} V fun (x_1 : V) =>
                              @Membership.mem.{0, 0} V (Finset.{0} V)
                                (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V))
                                (@Sensitivity213981Formal.ThreeBoundMinmaxCandidates.highHeads L I V inst_2 S F
                                  (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower L I V
                                    (@PartialOrder.toPreorder.{0} L
                                      (@SemilatticeInf.toPartialOrder.{0} L
                                        (@Lattice.toSemilatticeInf.{0} L
                                          (@DistribLattice.toLattice.{0} L
                                            (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                                    S F i j P)
                                  (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper L I V
                                    (@PartialOrder.toPreorder.{0} L
                                      (@SemilatticeInf.toPartialOrder.{0} L
                                        (@Lattice.toSemilatticeInf.{0} L
                                          (@DistribLattice.toLattice.{0} L
                                            (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                                    S F i j P)
                                  j x)
                                x_1))
                          (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts))
                          (fun (x_1 : Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts)) =>
                            @Subtype.{1} V fun (x_2 : V) =>
                              @Membership.mem.{0, 0} V (Finset.{0} V)
                                (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V))
                                (@Sensitivity213981Formal.ThreeBoundMinmaxCandidates.highHeads L I V inst_2 S F
                                  (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower L I V
                                    (@PartialOrder.toPreorder.{0} L
                                      (@SemilatticeInf.toPartialOrder.{0} L
                                        (@Lattice.toSemilatticeInf.{0} L
                                          (@DistribLattice.toLattice.{0} L
                                            (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                                    S F i j P)
                                  (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper L I V
                                    (@PartialOrder.toPreorder.{0} L
                                      (@SemilatticeInf.toPartialOrder.{0} L
                                        (@Lattice.toSemilatticeInf.{0} L
                                          (@DistribLattice.toLattice.{0} L
                                            (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                                    S F i j P)
                                  j x)
                                x_2)
                          (@EquivLike.toFunLike.{1, 1, 1}
                            (Equiv.{1, 1} (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts))
                              (@Subtype.{1} V fun (x_1 : V) =>
                                @Membership.mem.{0, 0} V (Finset.{0} V)
                                  (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V))
                                  (@Sensitivity213981Formal.ThreeBoundMinmaxCandidates.highHeads L I V inst_2 S F
                                    (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower L I V
                                      (@PartialOrder.toPreorder.{0} L
                                        (@SemilatticeInf.toPartialOrder.{0} L
                                          (@Lattice.toSemilatticeInf.{0} L
                                            (@DistribLattice.toLattice.{0} L
                                              (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                                      S F i j P)
                                    (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper L I V
                                      (@PartialOrder.toPreorder.{0} L
                                        (@SemilatticeInf.toPartialOrder.{0} L
                                          (@Lattice.toSemilatticeInf.{0} L
                                            (@DistribLattice.toLattice.{0} L
                                              (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                                      S F i j P)
                                    j x)
                                  x_1))
                            (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts))
                            (@Subtype.{1} V fun (x_1 : V) =>
                              @Membership.mem.{0, 0} V (Finset.{0} V)
                                (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V))
                                (@Sensitivity213981Formal.ThreeBoundMinmaxCandidates.highHeads L I V inst_2 S F
                                  (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower L I V
                                    (@PartialOrder.toPreorder.{0} L
                                      (@SemilatticeInf.toPartialOrder.{0} L
                                        (@Lattice.toSemilatticeInf.{0} L
                                          (@DistribLattice.toLattice.{0} L
                                            (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                                    S F i j P)
                                  (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper L I V
                                    (@PartialOrder.toPreorder.{0} L
                                      (@SemilatticeInf.toPartialOrder.{0} L
                                        (@Lattice.toSemilatticeInf.{0} L
                                          (@DistribLattice.toLattice.{0} L
                                            (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                                    S F i j P)
                                  j x)
                                x_1)
                            (@Equiv.instEquivLike.{1, 1}
                              (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts))
                              (@Subtype.{1} V fun (x_1 : V) =>
                                @Membership.mem.{0, 0} V (Finset.{0} V)
                                  (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V))
                                  (@Sensitivity213981Formal.ThreeBoundMinmaxCandidates.highHeads L I V inst_2 S F
                                    (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower L I V
                                      (@PartialOrder.toPreorder.{0} L
                                        (@SemilatticeInf.toPartialOrder.{0} L
                                          (@Lattice.toSemilatticeInf.{0} L
                                            (@DistribLattice.toLattice.{0} L
                                              (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                                      S F i j P)
                                    (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper L I V
                                      (@PartialOrder.toPreorder.{0} L
                                        (@SemilatticeInf.toPartialOrder.{0} L
                                          (@Lattice.toSemilatticeInf.{0} L
                                            (@DistribLattice.toLattice.{0} L
                                              (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                                      S F i j P)
                                    j x)
                                  x_1)))
                          e k))
                      (@Subtype.val.{1} V
                        (fun (x_1 : V) =>
                          @Membership.mem.{0, 0} V (Finset.{0} V)
                            (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V))
                            (@Sensitivity213981Formal.ThreeBoundMinmaxCandidates.highHeads L I V inst_2 S F
                              (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower L I V
                                (@PartialOrder.toPreorder.{0} L
                                  (@SemilatticeInf.toPartialOrder.{0} L
                                    (@Lattice.toSemilatticeInf.{0} L
                                      (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                                S F i j P)
                              (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper L I V
                                (@PartialOrder.toPreorder.{0} L
                                  (@SemilatticeInf.toPartialOrder.{0} L
                                    (@Lattice.toSemilatticeInf.{0} L
                                      (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                                S F i j P)
                              j x)
                            x_1)
                        (@DFunLike.coe.{1, 1, 1}
                          (Equiv.{1, 1} (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts))
                            (@Subtype.{1} V fun (x_1 : V) =>
                              @Membership.mem.{0, 0} V (Finset.{0} V)
                                (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V))
                                (@Sensitivity213981Formal.ThreeBoundMinmaxCandidates.highHeads L I V inst_2 S F
                                  (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower L I V
                                    (@PartialOrder.toPreorder.{0} L
                                      (@SemilatticeInf.toPartialOrder.{0} L
                                        (@Lattice.toSemilatticeInf.{0} L
                                          (@DistribLattice.toLattice.{0} L
                                            (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                                    S F i j P)
                                  (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper L I V
                                    (@PartialOrder.toPreorder.{0} L
                                      (@SemilatticeInf.toPartialOrder.{0} L
                                        (@Lattice.toSemilatticeInf.{0} L
                                          (@DistribLattice.toLattice.{0} L
                                            (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                                    S F i j P)
                                  j x)
                                x_1))
                          (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts))
                          (fun (x_1 : Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts)) =>
                            @Subtype.{1} V fun (x_2 : V) =>
                              @Membership.mem.{0, 0} V (Finset.{0} V)
                                (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V))
                                (@Sensitivity213981Formal.ThreeBoundMinmaxCandidates.highHeads L I V inst_2 S F
                                  (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower L I V
                                    (@PartialOrder.toPreorder.{0} L
                                      (@SemilatticeInf.toPartialOrder.{0} L
                                        (@Lattice.toSemilatticeInf.{0} L
                                          (@DistribLattice.toLattice.{0} L
                                            (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                                    S F i j P)
                                  (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper L I V
                                    (@PartialOrder.toPreorder.{0} L
                                      (@SemilatticeInf.toPartialOrder.{0} L
                                        (@Lattice.toSemilatticeInf.{0} L
                                          (@DistribLattice.toLattice.{0} L
                                            (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                                    S F i j P)
                                  j x)
                                x_2)
                          (@EquivLike.toFunLike.{1, 1, 1}
                            (Equiv.{1, 1} (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts))
                              (@Subtype.{1} V fun (x_1 : V) =>
                                @Membership.mem.{0, 0} V (Finset.{0} V)
                                  (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V))
                                  (@Sensitivity213981Formal.ThreeBoundMinmaxCandidates.highHeads L I V inst_2 S F
                                    (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower L I V
                                      (@PartialOrder.toPreorder.{0} L
                                        (@SemilatticeInf.toPartialOrder.{0} L
                                          (@Lattice.toSemilatticeInf.{0} L
                                            (@DistribLattice.toLattice.{0} L
                                              (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                                      S F i j P)
                                    (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper L I V
                                      (@PartialOrder.toPreorder.{0} L
                                        (@SemilatticeInf.toPartialOrder.{0} L
                                          (@Lattice.toSemilatticeInf.{0} L
                                            (@DistribLattice.toLattice.{0} L
                                              (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                                      S F i j P)
                                    j x)
                                  x_1))
                            (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts))
                            (@Subtype.{1} V fun (x_1 : V) =>
                              @Membership.mem.{0, 0} V (Finset.{0} V)
                                (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V))
                                (@Sensitivity213981Formal.ThreeBoundMinmaxCandidates.highHeads L I V inst_2 S F
                                  (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower L I V
                                    (@PartialOrder.toPreorder.{0} L
                                      (@SemilatticeInf.toPartialOrder.{0} L
                                        (@Lattice.toSemilatticeInf.{0} L
                                          (@DistribLattice.toLattice.{0} L
                                            (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                                    S F i j P)
                                  (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper L I V
                                    (@PartialOrder.toPreorder.{0} L
                                      (@SemilatticeInf.toPartialOrder.{0} L
                                        (@Lattice.toSemilatticeInf.{0} L
                                          (@DistribLattice.toLattice.{0} L
                                            (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                                    S F i j P)
                                  j x)
                                x_1)
                            (@Equiv.instEquivLike.{1, 1}
                              (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts))
                              (@Subtype.{1} V fun (x_1 : V) =>
                                @Membership.mem.{0, 0} V (Finset.{0} V)
                                  (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V))
                                  (@Sensitivity213981Formal.ThreeBoundMinmaxCandidates.highHeads L I V inst_2 S F
                                    (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower L I V
                                      (@PartialOrder.toPreorder.{0} L
                                        (@SemilatticeInf.toPartialOrder.{0} L
                                          (@Lattice.toSemilatticeInf.{0} L
                                            (@DistribLattice.toLattice.{0} L
                                              (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                                      S F i j P)
                                    (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper L I V
                                      (@PartialOrder.toPreorder.{0} L
                                        (@SemilatticeInf.toPartialOrder.{0} L
                                          (@Lattice.toSemilatticeInf.{0} L
                                            (@DistribLattice.toLattice.{0} L
                                              (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                                      S F i j P)
                                    j x)
                                  x_1)))
                          e l)))
                  fun (a b : Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts)) =>
                  Classical.propDecidable
                    (@Sensitivity213981Formal.ThreeBoundWitness.Stage.Adj L I V S
                      (@Subtype.val.{1} V
                        (fun (x_1 : V) =>
                          @Membership.mem.{0, 0} V (Finset.{0} V)
                            (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V))
                            (@Sensitivity213981Formal.ThreeBoundMinmaxCandidates.highHeads L I V inst_2 S F
                              (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower L I V
                                (@PartialOrder.toPreorder.{0} L
                                  (@SemilatticeInf.toPartialOrder.{0} L
                                    (@Lattice.toSemilatticeInf.{0} L
                                      (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                                S F i j P)
                              (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper L I V
                                (@PartialOrder.toPreorder.{0} L
                                  (@SemilatticeInf.toPartialOrder.{0} L
                                    (@Lattice.toSemilatticeInf.{0} L
                                      (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                                S F i j P)
                              j x)
                            x_1)
                        (@DFunLike.coe.{1, 1, 1}
                          (Equiv.{1, 1} (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts))
                            (@Subtype.{1} V fun (x_1 : V) =>
                              @Membership.mem.{0, 0} V (Finset.{0} V)
                                (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V))
                                (@Sensitivity213981Formal.ThreeBoundMinmaxCandidates.highHeads L I V inst_2 S F
                                  (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower L I V
                                    (@PartialOrder.toPreorder.{0} L
                                      (@SemilatticeInf.toPartialOrder.{0} L
                                        (@Lattice.toSemilatticeInf.{0} L
                                          (@DistribLattice.toLattice.{0} L
                                            (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                                    S F i j P)
                                  (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper L I V
                                    (@PartialOrder.toPreorder.{0} L
                                      (@SemilatticeInf.toPartialOrder.{0} L
                                        (@Lattice.toSemilatticeInf.{0} L
                                          (@DistribLattice.toLattice.{0} L
                                            (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                                    S F i j P)
                                  j x)
                                x_1))
                          (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts))
                          (fun (x_1 : Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts)) =>
                            @Subtype.{1} V fun (x_2 : V) =>
                              @Membership.mem.{0, 0} V (Finset.{0} V)
                                (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V))
                                (@Sensitivity213981Formal.ThreeBoundMinmaxCandidates.highHeads L I V inst_2 S F
                                  (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower L I V
                                    (@PartialOrder.toPreorder.{0} L
                                      (@SemilatticeInf.toPartialOrder.{0} L
                                        (@Lattice.toSemilatticeInf.{0} L
                                          (@DistribLattice.toLattice.{0} L
                                            (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                                    S F i j P)
                                  (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper L I V
                                    (@PartialOrder.toPreorder.{0} L
                                      (@SemilatticeInf.toPartialOrder.{0} L
                                        (@Lattice.toSemilatticeInf.{0} L
                                          (@DistribLattice.toLattice.{0} L
                                            (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                                    S F i j P)
                                  j x)
                                x_2)
                          (@EquivLike.toFunLike.{1, 1, 1}
                            (Equiv.{1, 1} (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts))
                              (@Subtype.{1} V fun (x_1 : V) =>
                                @Membership.mem.{0, 0} V (Finset.{0} V)
                                  (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V))
                                  (@Sensitivity213981Formal.ThreeBoundMinmaxCandidates.highHeads L I V inst_2 S F
                                    (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower L I V
                                      (@PartialOrder.toPreorder.{0} L
                                        (@SemilatticeInf.toPartialOrder.{0} L
                                          (@Lattice.toSemilatticeInf.{0} L
                                            (@DistribLattice.toLattice.{0} L
                                              (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                                      S F i j P)
                                    (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper L I V
                                      (@PartialOrder.toPreorder.{0} L
                                        (@SemilatticeInf.toPartialOrder.{0} L
                                          (@Lattice.toSemilatticeInf.{0} L
                                            (@DistribLattice.toLattice.{0} L
                                              (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                                      S F i j P)
                                    j x)
                                  x_1))
                            (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts))
                            (@Subtype.{1} V fun (x_1 : V) =>
                              @Membership.mem.{0, 0} V (Finset.{0} V)
                                (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V))
                                (@Sensitivity213981Formal.ThreeBoundMinmaxCandidates.highHeads L I V inst_2 S F
                                  (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower L I V
                                    (@PartialOrder.toPreorder.{0} L
                                      (@SemilatticeInf.toPartialOrder.{0} L
                                        (@Lattice.toSemilatticeInf.{0} L
                                          (@DistribLattice.toLattice.{0} L
                                            (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                                    S F i j P)
                                  (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper L I V
                                    (@PartialOrder.toPreorder.{0} L
                                      (@SemilatticeInf.toPartialOrder.{0} L
                                        (@Lattice.toSemilatticeInf.{0} L
                                          (@DistribLattice.toLattice.{0} L
                                            (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                                    S F i j P)
                                  j x)
                                x_1)
                            (@Equiv.instEquivLike.{1, 1}
                              (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts))
                              (@Subtype.{1} V fun (x_1 : V) =>
                                @Membership.mem.{0, 0} V (Finset.{0} V)
                                  (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V))
                                  (@Sensitivity213981Formal.ThreeBoundMinmaxCandidates.highHeads L I V inst_2 S F
                                    (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower L I V
                                      (@PartialOrder.toPreorder.{0} L
                                        (@SemilatticeInf.toPartialOrder.{0} L
                                          (@Lattice.toSemilatticeInf.{0} L
                                            (@DistribLattice.toLattice.{0} L
                                              (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                                      S F i j P)
                                    (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper L I V
                                      (@PartialOrder.toPreorder.{0} L
                                        (@SemilatticeInf.toPartialOrder.{0} L
                                          (@Lattice.toSemilatticeInf.{0} L
                                            (@DistribLattice.toLattice.{0} L
                                              (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                                      S F i j P)
                                    j x)
                                  x_1)))
                          e a))
                      (@Subtype.val.{1} V
                        (fun (x_1 : V) =>
                          @Membership.mem.{0, 0} V (Finset.{0} V)
                            (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V))
                            (@Sensitivity213981Formal.ThreeBoundMinmaxCandidates.highHeads L I V inst_2 S F
                              (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower L I V
                                (@PartialOrder.toPreorder.{0} L
                                  (@SemilatticeInf.toPartialOrder.{0} L
                                    (@Lattice.toSemilatticeInf.{0} L
                                      (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                                S F i j P)
                              (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper L I V
                                (@PartialOrder.toPreorder.{0} L
                                  (@SemilatticeInf.toPartialOrder.{0} L
                                    (@Lattice.toSemilatticeInf.{0} L
                                      (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                                S F i j P)
                              j x)
                            x_1)
                        (@DFunLike.coe.{1, 1, 1}
                          (Equiv.{1, 1} (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts))
                            (@Subtype.{1} V fun (x_1 : V) =>
                              @Membership.mem.{0, 0} V (Finset.{0} V)
                                (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V))
                                (@Sensitivity213981Formal.ThreeBoundMinmaxCandidates.highHeads L I V inst_2 S F
                                  (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower L I V
                                    (@PartialOrder.toPreorder.{0} L
                                      (@SemilatticeInf.toPartialOrder.{0} L
                                        (@Lattice.toSemilatticeInf.{0} L
                                          (@DistribLattice.toLattice.{0} L
                                            (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                                    S F i j P)
                                  (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper L I V
                                    (@PartialOrder.toPreorder.{0} L
                                      (@SemilatticeInf.toPartialOrder.{0} L
                                        (@Lattice.toSemilatticeInf.{0} L
                                          (@DistribLattice.toLattice.{0} L
                                            (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                                    S F i j P)
                                  j x)
                                x_1))
                          (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts))
                          (fun (x_1 : Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts)) =>
                            @Subtype.{1} V fun (x_2 : V) =>
                              @Membership.mem.{0, 0} V (Finset.{0} V)
                                (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V))
                                (@Sensitivity213981Formal.ThreeBoundMinmaxCandidates.highHeads L I V inst_2 S F
                                  (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower L I V
                                    (@PartialOrder.toPreorder.{0} L
                                      (@SemilatticeInf.toPartialOrder.{0} L
                                        (@Lattice.toSemilatticeInf.{0} L
                                          (@DistribLattice.toLattice.{0} L
                                            (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                                    S F i j P)
                                  (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper L I V
                                    (@PartialOrder.toPreorder.{0} L
                                      (@SemilatticeInf.toPartialOrder.{0} L
                                        (@Lattice.toSemilatticeInf.{0} L
                                          (@DistribLattice.toLattice.{0} L
                                            (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                                    S F i j P)
                                  j x)
                                x_2)
                          (@EquivLike.toFunLike.{1, 1, 1}
                            (Equiv.{1, 1} (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts))
                              (@Subtype.{1} V fun (x_1 : V) =>
                                @Membership.mem.{0, 0} V (Finset.{0} V)
                                  (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V))
                                  (@Sensitivity213981Formal.ThreeBoundMinmaxCandidates.highHeads L I V inst_2 S F
                                    (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower L I V
                                      (@PartialOrder.toPreorder.{0} L
                                        (@SemilatticeInf.toPartialOrder.{0} L
                                          (@Lattice.toSemilatticeInf.{0} L
                                            (@DistribLattice.toLattice.{0} L
                                              (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                                      S F i j P)
                                    (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper L I V
                                      (@PartialOrder.toPreorder.{0} L
                                        (@SemilatticeInf.toPartialOrder.{0} L
                                          (@Lattice.toSemilatticeInf.{0} L
                                            (@DistribLattice.toLattice.{0} L
                                              (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                                      S F i j P)
                                    j x)
                                  x_1))
                            (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts))
                            (@Subtype.{1} V fun (x_1 : V) =>
                              @Membership.mem.{0, 0} V (Finset.{0} V)
                                (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V))
                                (@Sensitivity213981Formal.ThreeBoundMinmaxCandidates.highHeads L I V inst_2 S F
                                  (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower L I V
                                    (@PartialOrder.toPreorder.{0} L
                                      (@SemilatticeInf.toPartialOrder.{0} L
                                        (@Lattice.toSemilatticeInf.{0} L
                                          (@DistribLattice.toLattice.{0} L
                                            (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                                    S F i j P)
                                  (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper L I V
                                    (@PartialOrder.toPreorder.{0} L
                                      (@SemilatticeInf.toPartialOrder.{0} L
                                        (@Lattice.toSemilatticeInf.{0} L
                                          (@DistribLattice.toLattice.{0} L
                                            (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                                    S F i j P)
                                  j x)
                                x_1)
                            (@Equiv.instEquivLike.{1, 1}
                              (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts))
                              (@Subtype.{1} V fun (x_1 : V) =>
                                @Membership.mem.{0, 0} V (Finset.{0} V)
                                  (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V))
                                  (@Sensitivity213981Formal.ThreeBoundMinmaxCandidates.highHeads L I V inst_2 S F
                                    (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower L I V
                                      (@PartialOrder.toPreorder.{0} L
                                        (@SemilatticeInf.toPartialOrder.{0} L
                                          (@Lattice.toSemilatticeInf.{0} L
                                            (@DistribLattice.toLattice.{0} L
                                              (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                                      S F i j P)
                                    (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper L I V
                                      (@PartialOrder.toPreorder.{0} L
                                        (@SemilatticeInf.toPartialOrder.{0} L
                                          (@Lattice.toSemilatticeInf.{0} L
                                            (@DistribLattice.toLattice.{0} L
                                              (@instDistribLatticeOfLinearOrder.{0} L inst)))))
                                      S F i j P)
                                    j x)
                                  x_1)))
                          e b)))))
              (@Membership.mem.{0, 0} (List.{0} Nat) (List.{0} (List.{0} Nat)) (@List.instMembership.{0} (List.{0} Nat))
                Sensitivity213981Formal.ThreeBoundQ3.records
                (Sensitivity213981Formal.ThreeBoundQ3.record
                  (@Prod.mk.{0, 0} (List.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind) (List.{0} Bool) ts ds))))) := by sorry
