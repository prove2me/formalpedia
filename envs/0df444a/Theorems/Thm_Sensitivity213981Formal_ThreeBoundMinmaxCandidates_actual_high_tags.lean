-- Prove2me | Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxCandidates_actual_high_tags
-- name    : Sensitivity213981Formal.ThreeBoundMinmaxCandidates.actual_high_tags
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-26T20:09:54.090802+00:00
-- url     : https://prove2.me/theorems/7ce0bcf4-1602-4c01-a7c3-f1c6e7372f64
-- title:
--   actual high tags — Boolean sensitivity certificate
-- statement:
--   The following universally quantified assertion holds for the finite sets, Boolean families, tournament data, and profile coordinates defined in the imported interfaces. Each binder specifies the domain of its variable, and bracketed conditions specify finite or ordered structures.
--
--   $$
--   \forall L:\mathcal U,\quad \forall I:\mathcal U,\quad \forall V:\mathcal U,\quad \bigl[\operatorname{LinearOrder}\bigl(L\bigr)\bigr]\;\bigl[\mathrm{finite}(I)\bigr]\;\bigl[\mathrm{finite}(V)\bigr]\;\forall S:\operatorname{Witness.Stage}\bigl(L, I, V\bigr),\quad \forall F:\left(L\to \left(\left(I\to \mathbb B\right)\to \mathbb B\right)\right),\quad \bigl(\operatorname{Profiles.Nested}\bigl(F\bigr)\Longrightarrow \forall i:L,\quad \forall j:L,\quad \forall P:\operatorname{MinmaxTransfer.PairData}\bigl(S, F, i, j\bigr),\quad \forall x:\left(V\times \mathbb B\times I\to \mathbb B\right),\quad \forall q:\mathbb N,\quad \bigl(\bigl(\operatorname{Stage.tolerance}\bigl(S, j\bigr) \le q\bigr)\Longrightarrow \exists \mathit{tag}:\left(V\to \operatorname{HighTypes.Kind}\bigl(q\bigr)\right),\quad \bigl(\forall w:V,\quad \bigl(w\in \operatorname{MinmaxCandidates.highHeads}\bigl(S, F, \operatorname{PairData.strongLower}\bigl(P\bigr), \operatorname{PairData.strongUpper}\bigl(P\bigr), j, x\bigr)\Longrightarrow \operatorname{HighTypes.OfKind}\bigl(q, \operatorname{MinmaxCandidates.PositiveCandidate}\bigl(S, F, \operatorname{PairData.strongLower}\bigl(P\bigr), \operatorname{PairData.strongUpper}\bigl(P\bigr), j, x, w\bigr), \operatorname{MinmaxCandidates.GuardCandidate}\bigl(S, F, \operatorname{PairData.strongLower}\bigl(P\bigr), \operatorname{PairData.strongUpper}\bigl(P\bigr), j, x, w\bigr), \mathit{tag}\bigl(w\bigr)\bigr)\bigr) \land \bigl(\forall w:V,\quad \bigl(w\in \operatorname{MinmaxCandidates.highHeads}\bigl(S, F, \operatorname{PairData.strongLower}\bigl(P\bigr), \operatorname{PairData.strongUpper}\bigl(P\bigr), j, x\bigr)\Longrightarrow \bigl(|\operatorname{Witness.failed}\bigl(S, F, j, x, w\bigr)| = \operatorname{HighTypes.budget}\bigl(q, \mathit{tag}\bigl(w\bigr)\bigr)\bigr)\bigr) \land \forall w:V,\quad \bigl(w\in \operatorname{MinmaxCandidates.highHeads}\bigl(S, F, \operatorname{PairData.strongLower}\bigl(P\bigr), \operatorname{PairData.strongUpper}\bigl(P\bigr), j, x\bigr)\Longrightarrow \bigl(|\operatorname{Finset.filter}\bigl(\operatorname{Stage.Adj}\bigl(S, w\bigr), \operatorname{MinmaxCandidates.highHeads}\bigl(S, F, \operatorname{PairData.strongLower}\bigl(P\bigr), \operatorname{PairData.strongUpper}\bigl(P\bigr), j, x\bigr)\bigr)| \le \operatorname{HighTypes.budget}\bigl(q, \mathit{tag}\bigl(w\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)
--   $$
--
--   Here $\mathbb B=\{\mathsf{false},\mathsf{true}\}$; $\mathcal P_{\mathrm{fin}}(X)$ denotes the finite subsets of $X$. Named functions and predicates refer to their definitions in the cited source. This result supplies the corresponding actual high tags step in the verified $22$-level sensitivity construction.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; MinmaxRepairCover.lean, lines 62–101.

import Definitions.Def_Sensitivity213981Formal_HighTypeCore
import Definitions.Def_Sensitivity213981Formal_MinmaxCandidates
import Definitions.Def_Sensitivity213981Formal_MinmaxPairData
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
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

theorem Sensitivity213981Formal.ThreeBoundMinmaxCandidates.actual_high_tags :
∀ {L I V : Type} [inst : LinearOrder.{0} L] [Fintype.{0} I] [inst_2 : Fintype.{0} V]
  (S : Sensitivity213981Formal.ThreeBoundWitness.Stage L I V) (F : L → (I → Bool) → Bool)
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
  (x : Prod.{0, 0} (Prod.{0, 0} V Bool) I → Bool) (q : Nat)
  (hq : @LE.le.{0} Nat instLENat (@Sensitivity213981Formal.ThreeBoundWitness.Stage.tolerance L I V S j) q),
  @Exists.{1} (V → Sensitivity213981Formal.ThreeBoundHighTypes.Kind q)
    fun (tag : V → Sensitivity213981Formal.ThreeBoundHighTypes.Kind q) =>
    And
      (∀ (w : V),
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
          Sensitivity213981Formal.ThreeBoundHighTypes.OfKind q
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
      (And
        (∀ (w : V),
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
            @Eq.{1} Nat (@Finset.card.{0} V (@Sensitivity213981Formal.ThreeBoundWitness.failed L I V inst_2 S F j x w))
              (Sensitivity213981Formal.ThreeBoundHighTypes.budget q (tag w)))
        (∀ (w : V),
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
            @LE.le.{0} Nat instLENat
              (@Finset.card.{0} V
                (@Finset.filter.{0} V (@Sensitivity213981Formal.ThreeBoundWitness.Stage.Adj L I V S w)
                  (fun (a : V) =>
                    Classical.propDecidable (@Sensitivity213981Formal.ThreeBoundWitness.Stage.Adj L I V S w a))
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
              (Sensitivity213981Formal.ThreeBoundHighTypes.budget q (tag w)))) := by sorry
