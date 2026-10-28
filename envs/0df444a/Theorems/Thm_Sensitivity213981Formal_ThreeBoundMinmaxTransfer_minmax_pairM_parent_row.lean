-- Prove2me | Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxTransfer_minmax_pairM_parent_row
-- name    : Sensitivity213981Formal.ThreeBoundMinmaxTransfer.minmax_pairM_parent_row
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-26T20:23:42.45356+00:00
-- url     : https://prove2.me/theorems/7a4db975-e6f1-4733-bf24-f19ad01e6f3c
-- title:
--   minmax pair M parent row — Boolean sensitivity certificate
-- statement:
--   The following universally quantified assertion holds for the finite sets, Boolean families, tournament data, and profile coordinates defined in the imported interfaces. Each binder specifies the domain of its variable, and bracketed conditions specify finite or ordered structures.
--
--   $$
--   \forall L:\mathcal U,\quad \forall I:\mathcal U,\quad \forall V:\mathcal U,\quad \bigl[\operatorname{LinearOrder}\bigl(L\bigr)\bigr]\;\bigl[\mathrm{finite}(I)\bigr]\;\bigl[\mathrm{finite}(V)\bigr]\;\forall S:\operatorname{Witness.Stage}\bigl(L, I, V\bigr),\quad \forall F:\left(L\to \left(\left(I\to \mathbb B\right)\to \mathbb B\right)\right),\quad \bigl(\operatorname{Profiles.Nested}\bigl(F\bigr)\Longrightarrow \forall i:L,\quad \forall j:L,\quad \forall k:L,\quad \forall P:\operatorname{MinmaxTransfer.PairData}\bigl(S, F, i, j\bigr),\quad \forall Q:\operatorname{MinmaxTransfer.PairData}\bigl(S, F, j, k\bigr),\quad \forall x:\left(V\times \mathbb B\times I\to \mathbb B\right),\quad \forall w:V,\quad \forall d:\mathbb N,\quad \forall \mathit{degree}:\mathbb N,\quad \bigl(\bigl(|\operatorname{Witness.failed}\bigl(S, F, j, x, w\bigr)| = d\bigr)\Longrightarrow \bigl(\bigl(d \le \operatorname{Stage.tolerance}\bigl(S, j\bigr)\bigr)\Longrightarrow \bigl(\bigl(d \le \operatorname{Stage.tolerance}\bigl(S, k\bigr)\bigr)\Longrightarrow \bigl(\bigl(\operatorname{MinmaxTransfer.mm}\bigl(F, \operatorname{PairData.strongLower}\bigl(P, d\bigr), \operatorname{PairData.strongUpper}\bigl(P, d\bigr), \operatorname{Witness.child}\bigl(x, w, \mathsf{false}\bigr), \operatorname{Witness.child}\bigl(x, w, \mathsf{true}\bigr)\bigr) = \mathsf{true}\bigr)\Longrightarrow \bigl(\bigl(\operatorname{Witness.parent}\bigl(S, F, k, x\bigr) = \mathsf{false}\bigr)\Longrightarrow \bigl(\bigl(|\operatorname{Positive.outgoing}\bigl(S, w\bigr)| = \mathit{degree}\bigr)\Longrightarrow \forall a:\mathbb N,\quad \forall \mathit{m0}:\mathbb N,\quad \forall \mathit{m1}:\mathbb N,\quad \forall \mathit{b0}:\mathbb N,\quad \forall \mathit{b1}:\mathbb N,\quad \forall p:\mathbb N,\quad \bigl(\operatorname{Profiles.ABound}\bigl(F, \operatorname{Stage.guard}\bigl(S, j\bigr), \operatorname{Stage.guard}\bigl(S, i\bigr), a\bigr)\Longrightarrow \bigl(\operatorname{Profiles.MBound}\bigl(F, \operatorname{PairData.weakLower}\bigl(P, d\bigr), \operatorname{PairData.strongLower}\bigl(P, d\bigr), \operatorname{PairData.strongLower}\bigl(Q, d\bigr), \mathit{m0}\bigr)\Longrightarrow \bigl(\operatorname{Profiles.MBound}\bigl(F, \operatorname{PairData.weakUpper}\bigl(P, d\bigr), \operatorname{PairData.strongUpper}\bigl(P, d\bigr), \operatorname{PairData.strongUpper}\bigl(Q, d\bigr), \mathit{m1}\bigr)\Longrightarrow \bigl(\operatorname{Profiles.BBound}\bigl(F, \operatorname{PairData.weakLower}\bigl(P, d\bigr), \operatorname{PairData.strongLower}\bigl(Q, d\bigr), \mathit{b0}\bigr)\Longrightarrow \bigl(\operatorname{Profiles.BBound}\bigl(F, \operatorname{PairData.weakUpper}\bigl(P, d\bigr), \operatorname{PairData.strongUpper}\bigl(Q, d\bigr), \mathit{b1}\bigr)\Longrightarrow \bigl(\operatorname{Profiles.PBound}\bigl(F, \operatorname{Stage.guard}\bigl(S, k\bigr), \operatorname{Stage.guard}\bigl(S, j\bigr), \operatorname{Stage.guard}\bigl(S, i\bigr), p\bigr)\Longrightarrow \bigl(|\operatorname{Profiles.flipsTo}\bigl(\operatorname{Witness.parent}\bigl(S, F, i\bigr), \mathsf{false}, x\bigr)| \le \operatorname{MinmaxTransfer.pairMCost}\bigl(\mathit{degree}, d, \operatorname{PairData.strongLower}\bigl(P, d\bigr), \operatorname{PairData.strongUpper}\bigl(P, d\bigr), \operatorname{PairData.strongLower}\bigl(Q, d\bigr), \operatorname{PairData.strongUpper}\bigl(Q, d\bigr), \operatorname{Stage.guard}\bigl(S, j\bigr), \operatorname{Stage.guard}\bigl(S, k\bigr), a, \mathit{m0}, \mathit{m1}, \mathit{b0}, \mathit{b1}, p\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)
--   $$
--
--   Here $\mathbb B=\{\mathsf{false},\mathsf{true}\}$; $\mathcal P_{\mathrm{fin}}(X)$ denotes the finite subsets of $X$. Named functions and predicates refer to their definitions in the cited source. This result supplies the corresponding minmax pair M parent row step in the verified $22$-level sensitivity construction.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; MinmaxMParent.lean, lines 48–77.

import Definitions.Def_Sensitivity213981Formal_MinmaxPairData
import Definitions.Def_Sensitivity213981Formal_MinmaxPairM
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
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

theorem Sensitivity213981Formal.ThreeBoundMinmaxTransfer.minmax_pairM_parent_row :
∀ {L I V : Type} [inst : LinearOrder.{0} L] [inst_1 : Fintype.{0} I] [inst_2 : Fintype.{0} V]
  (S : Sensitivity213981Formal.ThreeBoundWitness.Stage L I V) (F : L → (I → Bool) → Bool)
  (hF :
    @Sensitivity213981Formal.ThreeBoundProfiles.Nested L I
      (@PartialOrder.toPreorder.{0} L
        (@SemilatticeInf.toPartialOrder.{0} L
          (@Lattice.toSemilatticeInf.{0} L
            (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
      F)
  (i j k : L)
  (P :
    @Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData L I V
      (@PartialOrder.toPreorder.{0} L
        (@SemilatticeInf.toPartialOrder.{0} L
          (@Lattice.toSemilatticeInf.{0} L
            (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
      S F i j)
  (Q :
    @Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData L I V
      (@PartialOrder.toPreorder.{0} L
        (@SemilatticeInf.toPartialOrder.{0} L
          (@Lattice.toSemilatticeInf.{0} L
            (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
      S F j k)
  (x : Prod.{0, 0} (Prod.{0, 0} V Bool) I → Bool) (w : V) (d degree : Nat)
  (hd : @Eq.{1} Nat (@Finset.card.{0} V (@Sensitivity213981Formal.ThreeBoundWitness.failed L I V inst_2 S F j x w)) d)
  (hdj : @LE.le.{0} Nat instLENat d (@Sensitivity213981Formal.ThreeBoundWitness.Stage.tolerance L I V S j))
  (hdk : @LE.le.{0} Nat instLENat d (@Sensitivity213981Formal.ThreeBoundWitness.Stage.tolerance L I V S k))
  (hstrong :
    @Eq.{1} Bool
      (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.mm L I F
        (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower L I V
          (@PartialOrder.toPreorder.{0} L
            (@SemilatticeInf.toPartialOrder.{0} L
              (@Lattice.toSemilatticeInf.{0} L
                (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
          S F i j P d)
        (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper L I V
          (@PartialOrder.toPreorder.{0} L
            (@SemilatticeInf.toPartialOrder.{0} L
              (@Lattice.toSemilatticeInf.{0} L
                (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
          S F i j P d)
        (@Sensitivity213981Formal.ThreeBoundWitness.child I V x w Bool.false)
        (@Sensitivity213981Formal.ThreeBoundWitness.child I V x w Bool.true))
      Bool.true)
  (hxk : @Eq.{1} Bool (@Sensitivity213981Formal.ThreeBoundWitness.parent L I V inst_2 S F k x) Bool.false)
  (hdegree :
    @Eq.{1} Nat (@Finset.card.{0} V (@Sensitivity213981Formal.ThreeBoundPositive.outgoing L I V inst_2 S w)) degree)
  (a m0 m1 b0 b1 p : Nat)
  (ha :
    @Sensitivity213981Formal.ThreeBoundProfiles.ABound L I inst_1 F
      (@Sensitivity213981Formal.ThreeBoundWitness.Stage.guard L I V S j)
      (@Sensitivity213981Formal.ThreeBoundWitness.Stage.guard L I V S i) a)
  (hm0 :
    @Sensitivity213981Formal.ThreeBoundProfiles.MBound L I inst_1 F
      (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.weakLower L I V
        (@PartialOrder.toPreorder.{0} L
          (@SemilatticeInf.toPartialOrder.{0} L
            (@Lattice.toSemilatticeInf.{0} L
              (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
        S F i j P d)
      (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower L I V
        (@PartialOrder.toPreorder.{0} L
          (@SemilatticeInf.toPartialOrder.{0} L
            (@Lattice.toSemilatticeInf.{0} L
              (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
        S F i j P d)
      (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower L I V
        (@PartialOrder.toPreorder.{0} L
          (@SemilatticeInf.toPartialOrder.{0} L
            (@Lattice.toSemilatticeInf.{0} L
              (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
        S F j k Q d)
      m0)
  (hm1 :
    @Sensitivity213981Formal.ThreeBoundProfiles.MBound L I inst_1 F
      (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.weakUpper L I V
        (@PartialOrder.toPreorder.{0} L
          (@SemilatticeInf.toPartialOrder.{0} L
            (@Lattice.toSemilatticeInf.{0} L
              (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
        S F i j P d)
      (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper L I V
        (@PartialOrder.toPreorder.{0} L
          (@SemilatticeInf.toPartialOrder.{0} L
            (@Lattice.toSemilatticeInf.{0} L
              (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
        S F i j P d)
      (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper L I V
        (@PartialOrder.toPreorder.{0} L
          (@SemilatticeInf.toPartialOrder.{0} L
            (@Lattice.toSemilatticeInf.{0} L
              (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
        S F j k Q d)
      m1)
  (hb0 :
    @Sensitivity213981Formal.ThreeBoundProfiles.BBound L I inst_1 F
      (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.weakLower L I V
        (@PartialOrder.toPreorder.{0} L
          (@SemilatticeInf.toPartialOrder.{0} L
            (@Lattice.toSemilatticeInf.{0} L
              (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
        S F i j P d)
      (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower L I V
        (@PartialOrder.toPreorder.{0} L
          (@SemilatticeInf.toPartialOrder.{0} L
            (@Lattice.toSemilatticeInf.{0} L
              (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
        S F j k Q d)
      b0)
  (hb1 :
    @Sensitivity213981Formal.ThreeBoundProfiles.BBound L I inst_1 F
      (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.weakUpper L I V
        (@PartialOrder.toPreorder.{0} L
          (@SemilatticeInf.toPartialOrder.{0} L
            (@Lattice.toSemilatticeInf.{0} L
              (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
        S F i j P d)
      (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper L I V
        (@PartialOrder.toPreorder.{0} L
          (@SemilatticeInf.toPartialOrder.{0} L
            (@Lattice.toSemilatticeInf.{0} L
              (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
        S F j k Q d)
      b1)
  (hp :
    @Sensitivity213981Formal.ThreeBoundProfiles.PBound L I inst_1 F
      (@Sensitivity213981Formal.ThreeBoundWitness.Stage.guard L I V S k)
      (@Sensitivity213981Formal.ThreeBoundWitness.Stage.guard L I V S j)
      (@Sensitivity213981Formal.ThreeBoundWitness.Stage.guard L I V S i) p),
  @LE.le.{0} Nat instLENat
    (@Finset.card.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I)
      (@Sensitivity213981Formal.ThreeBoundProfiles.flipsTo (Prod.{0, 0} (Prod.{0, 0} V Bool) I)
        (@instFintypeProd.{0, 0} (Prod.{0, 0} V Bool) I (@instFintypeProd.{0, 0} V Bool inst_2 Bool.fintype) inst_1)
        (@Sensitivity213981Formal.ThreeBoundWitness.parent L I V inst_2 S F i) Bool.false x))
    (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.pairMCost L inst degree d
      (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower L I V
        (@PartialOrder.toPreorder.{0} L
          (@SemilatticeInf.toPartialOrder.{0} L
            (@Lattice.toSemilatticeInf.{0} L
              (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
        S F i j P d)
      (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper L I V
        (@PartialOrder.toPreorder.{0} L
          (@SemilatticeInf.toPartialOrder.{0} L
            (@Lattice.toSemilatticeInf.{0} L
              (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
        S F i j P d)
      (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower L I V
        (@PartialOrder.toPreorder.{0} L
          (@SemilatticeInf.toPartialOrder.{0} L
            (@Lattice.toSemilatticeInf.{0} L
              (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
        S F j k Q d)
      (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper L I V
        (@PartialOrder.toPreorder.{0} L
          (@SemilatticeInf.toPartialOrder.{0} L
            (@Lattice.toSemilatticeInf.{0} L
              (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
        S F j k Q d)
      (@Sensitivity213981Formal.ThreeBoundWitness.Stage.guard L I V S j)
      (@Sensitivity213981Formal.ThreeBoundWitness.Stage.guard L I V S k) a m0 m1 b0 b1 p) := by sorry
