-- Prove2me | Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxCandidates_repair_cover
-- name    : Sensitivity213981Formal.ThreeBoundMinmaxCandidates.repair_cover
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-26T20:09:42.873079+00:00
-- url     : https://prove2.me/theorems/1ccfee8d-961a-4586-a65f-066912806816
-- title:
--   repair cover — Boolean sensitivity certificate
-- statement:
--   The following universally quantified assertion holds for the finite sets, Boolean families, tournament data, and profile coordinates defined in the imported interfaces. Each binder specifies the domain of its variable, and bracketed conditions specify finite or ordered structures.
--
--   $$
--   \forall L:\mathcal U,\quad \forall I:\mathcal U,\quad \forall V:\mathcal U,\quad \bigl[\operatorname{LinearOrder}\bigl(L\bigr)\bigr]\;\bigl[\mathrm{finite}(I)\bigr]\;\bigl[\mathrm{finite}(V)\bigr]\;\forall S:\operatorname{Witness.Stage}\bigl(L, I, V\bigr),\quad \forall F:\left(L\to \left(\left(I\to \mathbb B\right)\to \mathbb B\right)\right),\quad \bigl(\operatorname{Profiles.Nested}\bigl(F\bigr)\Longrightarrow \forall i:L,\quad \forall j:L,\quad \forall P:\operatorname{MinmaxTransfer.PairData}\bigl(S, F, i, j\bigr),\quad \forall x:\left(V\times \mathbb B\times I\to \mathbb B\right),\quad \forall w:V,\quad \forall c:\mathbb B,\quad \forall a:I,\quad \bigl(\bigl(\operatorname{Witness.parent}\bigl(S, F, j, x\bigr) = \mathsf{false}\bigr)\Longrightarrow \bigl(\bigl(\operatorname{Witness.parent}\bigl(S, F, j, \operatorname{Paper320.flip}\bigl(x, \operatorname{Singleton.singleton}\bigl(((w,c),a)\bigr)\bigr)\bigr) = \mathsf{true}\bigr)\Longrightarrow \bigl(\exists b:\mathbb N,\quad \bigl(\operatorname{MinmaxCandidates.TargetCandidate}\bigl(S, F, \operatorname{PairData.strongLower}\bigl(P\bigr), \operatorname{PairData.strongUpper}\bigl(P\bigr), j, x, w, b\bigr) \land a\in \operatorname{MinmaxHeads.upPart}\bigl(F, \operatorname{PairData.strongLower}\bigl(P, b\bigr), \operatorname{PairData.strongUpper}\bigl(P, b\bigr), \operatorname{Witness.child}\bigl(x, w\bigr), c\bigr)\bigr) \lor \exists v:V,\quad \exists b:\mathbb N,\quad \bigl(\operatorname{MinmaxCandidates.GuardCandidate}\bigl(S, F, \operatorname{PairData.strongLower}\bigl(P\bigr), \operatorname{PairData.strongUpper}\bigl(P\bigr), j, x, v, b\bigr) \land \bigl(\operatorname{Stage.Adj}\bigl(S, v, w\bigr) \land \bigl(\bigl(\operatorname{Stage.label}\bigl(S, v, w\bigr) = c\bigr) \land \bigl(\bigl(F\bigl(\operatorname{Stage.guard}\bigl(S, j\bigr), \operatorname{Witness.child}\bigl(x, w, c\bigr)\bigr) = \mathsf{true}\bigr) \land a\in \operatorname{Profiles.flipsTo}\bigl(F\bigl(\operatorname{Stage.guard}\bigl(S, j\bigr)\bigr), \mathsf{false}, \operatorname{Witness.child}\bigl(x, w, c\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)
--   $$
--
--   Here $\mathbb B=\{\mathsf{false},\mathsf{true}\}$; $\mathcal P_{\mathrm{fin}}(X)$ denotes the finite subsets of $X$. Named functions and predicates refer to their definitions in the cited source. This result supplies the corresponding repair cover step in the verified $22$-level sensitivity construction.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; MinmaxRepairCover.lean, lines 17–60.

import Definitions.Def_Sensitivity213981Formal_GuardAugmentation
import Definitions.Def_Sensitivity213981Formal_MinmaxCandidates
import Definitions.Def_Sensitivity213981Formal_MinmaxPairData
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_Supplement_GradedPositiveBoundary
import Definitions.Def_Sensitivity213981Formal_Supplement_Q2Enumeration
import Definitions.Def_Sensitivity213981Formal_WitnessLifting
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

theorem Sensitivity213981Formal.ThreeBoundMinmaxCandidates.repair_cover :
∀ {L I V : Type} [inst : LinearOrder.{0} L] [inst_1 : Fintype.{0} I] [inst_2 : Fintype.{0} V]
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
  (x : Prod.{0, 0} (Prod.{0, 0} V Bool) I → Bool) (w : V) (c : Bool) (a : I)
  (hoff : @Eq.{1} Bool (@Sensitivity213981Formal.ThreeBoundWitness.parent L I V inst_2 S F j x) Bool.false)
  (hon :
    @Eq.{1} Bool
      (@Sensitivity213981Formal.ThreeBoundWitness.parent L I V inst_2 S F j
        (@OAI.Paper320.flip (Prod.{0, 0} (Prod.{0, 0} V Bool) I) x
          (@Singleton.singleton.{0, 0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I)
            (Finset.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I))
            (@Finset.instSingleton.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I))
            (@Prod.mk.{0, 0} (Prod.{0, 0} V Bool) I (@Prod.mk.{0, 0} V Bool w c) a))))
      Bool.true),
  Or
    (@Exists.{1} Nat fun (b : Nat) =>
      And
        (@Sensitivity213981Formal.ThreeBoundMinmaxCandidates.TargetCandidate L I V inst_2 S F
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
          j x w b)
        (@Membership.mem.{0, 0} I (Finset.{0} I)
          (@SetLike.instMembership.{0, 0} (Finset.{0} I) I (@Finset.instSetLike.{0} I))
          (@Sensitivity213981Formal.ThreeBoundMinmaxHeads.upPart L I inst_1 F
            (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower L I V
              (@PartialOrder.toPreorder.{0} L
                (@SemilatticeInf.toPartialOrder.{0} L
                  (@Lattice.toSemilatticeInf.{0} L
                    (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
              S F i j P b)
            (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper L I V
              (@PartialOrder.toPreorder.{0} L
                (@SemilatticeInf.toPartialOrder.{0} L
                  (@Lattice.toSemilatticeInf.{0} L
                    (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
              S F i j P b)
            (@Sensitivity213981Formal.ThreeBoundWitness.child I V x w) c)
          a))
    (@Exists.{1} V fun (v : V) =>
      @Exists.{1} Nat fun (b : Nat) =>
        And
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
            j x v b)
          (And (@Sensitivity213981Formal.ThreeBoundWitness.Stage.Adj L I V S v w)
            (And (@Eq.{1} Bool (@Sensitivity213981Formal.ThreeBoundWitness.Stage.label L I V S v w) c)
              (And
                (@Eq.{1} Bool
                  (F (@Sensitivity213981Formal.ThreeBoundWitness.Stage.guard L I V S j)
                    (@Sensitivity213981Formal.ThreeBoundWitness.child I V x w c))
                  Bool.true)
                (@Membership.mem.{0, 0} I (Finset.{0} I)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} I) I (@Finset.instSetLike.{0} I))
                  (@Sensitivity213981Formal.ThreeBoundProfiles.flipsTo I inst_1
                    (F (@Sensitivity213981Formal.ThreeBoundWitness.Stage.guard L I V S j)) Bool.false
                    (@Sensitivity213981Formal.ThreeBoundWitness.child I V x w c))
                  a))))) := by sorry
