-- Prove2me | Theorems.Thm_Sensitivity213981Formal_ThreeBoundRankNumeric_actual_capPrefix
-- name    : Sensitivity213981Formal.ThreeBoundRankNumeric.actual_capPrefix
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-26T20:26:06.908255+00:00
-- url     : https://prove2.me/theorems/471c0f20-3150-45ff-9402-192aa504960a
-- title:
--   actual cap Prefix — Boolean sensitivity certificate
-- statement:
--   The following universally quantified assertion holds for the finite sets, Boolean families, tournament data, and profile coordinates defined in the imported interfaces. Each binder specifies the domain of its variable, and bracketed conditions specify finite or ordered structures.
--
--   $$
--   \forall L:\mathcal U,\quad \forall I:\mathcal U,\quad \forall V:\mathcal U,\quad \bigl[\operatorname{LinearOrder}\bigl(L\bigr)\bigr]\;\bigl[\mathrm{finite}(I)\bigr]\;\bigl[\mathrm{finite}(V)\bigr]\;\forall S:\operatorname{Witness.Stage}\bigl(L, I, V\bigr),\quad \bigl(\operatorname{TournamentHighRows.IsTournament}\bigl(\operatorname{Stage.Adj}\bigl(S\bigr)\bigr)\Longrightarrow \forall F:\left(L\to \left(\left(I\to \mathbb B\right)\to \mathbb B\right)\right),\quad \bigl(\operatorname{Profiles.Nested}\bigl(F\bigr)\Longrightarrow \forall i:L,\quad \forall j:L,\quad \forall P:\operatorname{MinmaxTransfer.PairData}\bigl(S, F, i, j\bigr),\quad \forall \mathit{input}:\left(V\times \mathbb B\times I\to \mathbb B\right),\quad \bigl(\bigl(\operatorname{Stage.tolerance}\bigl(S, j\bigr) \le 3\bigr)\Longrightarrow \forall \mathit{tag}:\left(V\to \{0,\ldots,11-1\}\right),\quad \bigl(\forall w:V,\quad \bigl(w\in \operatorname{MinmaxCandidates.highHeads}\bigl(S, F, \operatorname{PairData.strongLower}\bigl(P\bigr), \operatorname{PairData.strongUpper}\bigl(P\bigr), j, \mathit{input}\bigr)\Longrightarrow \operatorname{HighTypes.OfKind}\bigl(3, \operatorname{MinmaxCandidates.PositiveCandidate}\bigl(S, F, \operatorname{PairData.strongLower}\bigl(P\bigr), \operatorname{PairData.strongUpper}\bigl(P\bigr), j, \mathit{input}, w\bigr), \operatorname{MinmaxCandidates.GuardCandidate}\bigl(S, F, \operatorname{PairData.strongLower}\bigl(P\bigr), \operatorname{PairData.strongUpper}\bigl(P\bigr), j, \mathit{input}, w\bigr), \mathit{tag}\bigl(w\bigr)\bigr)\bigr)\Longrightarrow \bigl(\forall w:V,\quad \bigl(w\in \operatorname{MinmaxCandidates.highHeads}\bigl(S, F, \operatorname{PairData.strongLower}\bigl(P\bigr), \operatorname{PairData.strongUpper}\bigl(P\bigr), j, \mathit{input}\bigr)\Longrightarrow \bigl(|\operatorname{Witness.failed}\bigl(S, F, j, \mathit{input}, w\bigr)| = \operatorname{HighTypes.budget}\bigl(3, \mathit{tag}\bigl(w\bigr)\bigr)\bigr)\bigr)\Longrightarrow \forall \mathit{caps}:\operatorname{Numeric.Caps},\quad \forall \mathit{perfect}:\mathbb N,\quad \bigl(\operatorname{RankNumeric.CapsSound}\bigl(\operatorname{Stage.Adj}\bigl(S\bigr), \operatorname{Stage.label}\bigl(S\bigr), \mathit{caps}, \mathit{perfect}\bigr)\Longrightarrow \forall r:\operatorname{RankNumeric.Record},\quad \bigl(\forall k:\{0,\ldots,11-1\},\quad \bigl(r\bigl(k\bigr) = \operatorname{Accounting.typeCount}\bigl(\operatorname{MinmaxCandidates.highHeads}\bigl(S, F, \operatorname{PairData.strongLower}\bigl(P\bigr), \operatorname{PairData.strongUpper}\bigl(P\bigr), j, \mathit{input}\bigr), \mathit{tag}, k\bigr)\bigr)\Longrightarrow \bigl(\forall k:\{0,\ldots,7-1\},\quad \bigl(\bigl(\bigl(k+1\bigr) \le |\operatorname{MinmaxCandidates.highHeads}\bigl(S, F, \operatorname{PairData.strongLower}\bigl(P\bigr), \operatorname{PairData.strongUpper}\bigl(P\bigr), j, \mathit{input}\bigr)|\bigr)\Longrightarrow \bigl(r\bigl(\bigl(34+k\bigr)\bigr) = \operatorname{MinmaxCaps.residualPrefix}\bigl(S, F, \operatorname{PairData.strongLower}\bigl(P\bigr), \operatorname{PairData.strongUpper}\bigl(P\bigr), j, \mathit{input}, \bigl(k+1\bigr)\bigr)\bigr)\bigr)\Longrightarrow \forall q:\mathbb N,\quad \bigl(\bigl(q \le 3\bigr)\Longrightarrow \bigl(|\operatorname{MinmaxCandidates.targetPrefix}\bigl(S, F, \operatorname{PairData.strongLower}\bigl(P\bigr), \operatorname{PairData.strongUpper}\bigl(P\bigr), j, \mathit{input}, q\bigr)| \le \operatorname{RankNumeric.capPrefix}\bigl(\mathit{caps}, r, q\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)
--   $$
--
--   Here $\mathbb B=\{\mathsf{false},\mathsf{true}\}$; $\mathcal P_{\mathrm{fin}}(X)$ denotes the finite subsets of $X$. Named functions and predicates refer to their definitions in the cited source. This result supplies the corresponding actual cap Prefix step in the verified $22$-level sensitivity construction.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; RankRecordCaps.lean, lines 18–110.

import Definitions.Def_Sensitivity213981Formal_ActualPrefixCaps
import Definitions.Def_Sensitivity213981Formal_GlobalAccounting
import Definitions.Def_Sensitivity213981Formal_GradedCandidates
import Definitions.Def_Sensitivity213981Formal_HighTypeCore
import Definitions.Def_Sensitivity213981Formal_MinmaxCandidates
import Definitions.Def_Sensitivity213981Formal_MinmaxPairData
import Definitions.Def_Sensitivity213981Formal_MinmaxPrefixCaps
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_Q2EnumerationBridge
import Definitions.Def_Sensitivity213981Formal_RankCapData
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

theorem Sensitivity213981Formal.ThreeBoundRankNumeric.actual_capPrefix :
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
  (input : Prod.{0, 0} (Prod.{0, 0} V Bool) I → Bool)
  (hQ :
    @LE.le.{0} Nat instLENat (@Sensitivity213981Formal.ThreeBoundWitness.Stage.tolerance L I V S j)
      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
  (tag : V → Fin (@OfNat.ofNat.{0} Nat (nat_lit 11) (instOfNatNat (nat_lit 11))))
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
            j input)
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
            j input w)
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
            j input w)
          (tag w))
  (hc :
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
            j input)
          w →
        @Eq.{1} Nat (@Finset.card.{0} V (@Sensitivity213981Formal.ThreeBoundWitness.failed L I V inst_2 S F j input w))
          (Sensitivity213981Formal.ThreeBoundHighTypes.budget
            (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) (tag w)))
  (caps : Sensitivity213981Formal.ThreeBoundNumeric.Caps) (perfect : Nat)
  (hcap :
    @Sensitivity213981Formal.ThreeBoundRankNumeric.CapsSound V inst_2
      (fun (a b : V) => Classical.propDecidable (@Eq.{1} V a b))
      (@Sensitivity213981Formal.ThreeBoundWitness.Stage.Adj L I V S)
      (@Sensitivity213981Formal.ThreeBoundWitness.Stage.label L I V S) caps perfect)
  (r : Sensitivity213981Formal.ThreeBoundRankNumeric.Record)
  (hx :
    ∀ (k : Fin (@OfNat.ofNat.{0} Nat (nat_lit 11) (instOfNatNat (nat_lit 11)))),
      @Eq.{1} Nat (r (@Fin.val (@OfNat.ofNat.{0} Nat (nat_lit 11) (instOfNatNat (nat_lit 11))) k))
        (@Sensitivity213981Formal.ThreeBoundAccounting.typeCount V
          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 11) (instOfNatNat (nat_lit 11))))
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
            j input)
          tag k))
  (hrs :
    ∀ (k : Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))),
      @LE.le.{0} Nat instLENat
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@Fin.val (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))) k)
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@Finset.card.{0} V
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
              j input)) →
        @Eq.{1} Nat
          (r
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 34) (instOfNatNat (nat_lit 34)))
              (@Fin.val (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))) k)))
          (@Sensitivity213981Formal.ThreeBoundMinmaxCaps.residualPrefix L I V inst_2 S F
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
            j input
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@Fin.val (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))) k)
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (q : Nat) (hq : @LE.le.{0} Nat instLENat q (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))),
  @LE.le.{0} Nat instLENat
    (@Finset.card.{0} V
      (@Sensitivity213981Formal.ThreeBoundMinmaxCandidates.targetPrefix L I V inst_2 S F
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
        j input q))
    (Sensitivity213981Formal.ThreeBoundRankNumeric.capPrefix caps r q) := by sorry
