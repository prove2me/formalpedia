-- Prove2me | Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxTransfer_minmax_strictD_parent
-- name    : Sensitivity213981Formal.ThreeBoundMinmaxTransfer.minmax_strictD_parent
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-26T20:28:16.293365+00:00
-- url     : https://prove2.me/theorems/c3a7f319-e65d-42d9-bf61-4757ad1f1e3b
-- title:
--   minmax strict D parent — Boolean sensitivity certificate
-- statement:
--   The following universally quantified assertion holds for the finite sets, Boolean families, tournament data, and profile coordinates defined in the imported interfaces. Each binder specifies the domain of its variable, and bracketed conditions specify finite or ordered structures.
--
--   $$
--   \forall L:\mathcal U,\quad \forall I:\mathcal U,\quad \forall V:\mathcal U,\quad \bigl[\operatorname{LinearOrder}\bigl(L\bigr)\bigr]\;\bigl[\mathrm{finite}(I)\bigr]\;\bigl[\mathrm{finite}(V)\bigr]\;\forall S:\operatorname{Witness.Stage}\bigl(L, I, V\bigr),\quad \bigl(\operatorname{TournamentHighRows.IsTournament}\bigl(\operatorname{Stage.Adj}\bigl(S\bigr)\bigr)\Longrightarrow \forall F:\left(L\to \left(\left(I\to \mathbb B\right)\to \mathbb B\right)\right),\quad \bigl(\operatorname{Profiles.Nested}\bigl(F\bigr)\Longrightarrow \forall i:L,\quad \forall j:L,\quad \forall k:L,\quad \forall l:L,\quad \forall P:\operatorname{MinmaxTransfer.PairData}\bigl(S, F, i, j\bigr),\quad \forall Q:\operatorname{MinmaxTransfer.PairData}\bigl(S, F, j, k\bigr),\quad \bigl(\bigl(\operatorname{Stage.tolerance}\bigl(S, j\bigr) = 0\bigr)\Longrightarrow \bigl(\bigl(\operatorname{Stage.tolerance}\bigl(S, l\bigr) = 0\bigr)\Longrightarrow \forall \mathit{tl}:L,\quad \bigl(\forall u:\left(I\to \mathbb B\right),\quad \forall z:\left(I\to \mathbb B\right),\quad \bigl(\operatorname{Stage.target}\bigl(S, l, 0, u, z\bigr) = \operatorname{MinmaxTransfer.mm}\bigl(F, \mathit{tl}, \mathit{tl}, u, z\bigr)\bigr)\Longrightarrow \bigl(\bigl(\operatorname{PairData.strongUpper}\bigl(P, 0\bigr) \le \mathit{tl}\bigr)\Longrightarrow \bigl(\bigl(\operatorname{PairData.strongUpper}\bigl(Q, 0\bigr) \le \mathit{tl}\bigr)\Longrightarrow \bigl(\bigl(\operatorname{Stage.guard}\bigl(S, l\bigr) \le \operatorname{Stage.guard}\bigl(S, k\bigr)\bigr)\Longrightarrow \forall \mathit{degree}:\mathbb N,\quad \forall \mathit{aM}:\mathbb N,\quad \forall \mathit{m0}:\mathbb N,\quad \forall \mathit{m1}:\mathbb N,\quad \forall \mathit{bm0}:\mathbb N,\quad \forall \mathit{bm1}:\mathbb N,\quad \forall p:\mathbb N,\quad \forall \mathit{b0}:\mathbb N,\quad \forall \mathit{b1}:\mathbb N,\quad \forall \mathit{aD}:\mathbb N,\quad \forall \mathit{dt}:\mathbb N,\quad \forall \mathit{dg}:\mathbb N,\quad \bigl(\forall v:V,\quad \bigl(|\operatorname{Positive.outgoing}\bigl(S, v\bigr)| = \mathit{degree}\bigr)\Longrightarrow \bigl(\operatorname{Profiles.ABound}\bigl(F, \operatorname{Stage.guard}\bigl(S, j\bigr), \operatorname{Stage.guard}\bigl(S, i\bigr), \mathit{aM}\bigr)\Longrightarrow \bigl(\operatorname{Profiles.MBound}\bigl(F, \operatorname{PairData.weakLower}\bigl(P, 0\bigr), \operatorname{PairData.strongLower}\bigl(P, 0\bigr), \operatorname{PairData.strongLower}\bigl(Q, 0\bigr), \mathit{m0}\bigr)\Longrightarrow \bigl(\operatorname{Profiles.MBound}\bigl(F, \operatorname{PairData.weakUpper}\bigl(P, 0\bigr), \operatorname{PairData.strongUpper}\bigl(P, 0\bigr), \operatorname{PairData.strongUpper}\bigl(Q, 0\bigr), \mathit{m1}\bigr)\Longrightarrow \bigl(\operatorname{Profiles.BBound}\bigl(F, \operatorname{PairData.weakLower}\bigl(P, 0\bigr), \operatorname{PairData.strongLower}\bigl(Q, 0\bigr), \mathit{bm0}\bigr)\Longrightarrow \bigl(\operatorname{Profiles.BBound}\bigl(F, \operatorname{PairData.weakUpper}\bigl(P, 0\bigr), \operatorname{PairData.strongUpper}\bigl(Q, 0\bigr), \mathit{bm1}\bigr)\Longrightarrow \bigl(\operatorname{Profiles.PBound}\bigl(F, \operatorname{Stage.guard}\bigl(S, k\bigr), \operatorname{Stage.guard}\bigl(S, j\bigr), \operatorname{Stage.guard}\bigl(S, i\bigr), p\bigr)\Longrightarrow \bigl(\operatorname{Profiles.BBound}\bigl(F, \operatorname{PairData.weakLower}\bigl(P, 0\bigr), \mathit{tl}, \mathit{b0}\bigr)\Longrightarrow \bigl(\operatorname{Profiles.BBound}\bigl(F, \operatorname{PairData.weakUpper}\bigl(P, 0\bigr), \mathit{tl}, \mathit{b1}\bigr)\Longrightarrow \bigl(\operatorname{Profiles.ABound}\bigl(F, \operatorname{Stage.guard}\bigl(S, l\bigr), \operatorname{Stage.guard}\bigl(S, i\bigr), \mathit{aD}\bigr)\Longrightarrow \bigl(\operatorname{Profiles.DBound}\bigl(F, \operatorname{PairData.weakLower}\bigl(P, 0\bigr), \operatorname{PairData.strongLower}\bigl(P, 0\bigr), \operatorname{PairData.strongLower}\bigl(Q, 0\bigr), \mathit{tl}, \mathit{dt}\bigr)\Longrightarrow \bigl(\operatorname{Profiles.DBound}\bigl(F, \operatorname{Stage.guard}\bigl(S, l\bigr), \operatorname{Stage.guard}\bigl(S, k\bigr), \operatorname{Stage.guard}\bigl(S, j\bigr), \operatorname{Stage.guard}\bigl(S, i\bigr), \mathit{dg}\bigr)\Longrightarrow \operatorname{Profiles.DBound}\bigl(\operatorname{Witness.parent}\bigl(S, F\bigr), i, j, k, l, \operatorname{Max.max}\bigl(\operatorname{MinmaxTransfer.pairMCost}\bigl(\mathit{degree}, 0, \operatorname{PairData.strongLower}\bigl(P, 0\bigr), \operatorname{PairData.strongUpper}\bigl(P, 0\bigr), \operatorname{PairData.strongLower}\bigl(Q, 0\bigr), \operatorname{PairData.strongUpper}\bigl(Q, 0\bigr), \operatorname{Stage.guard}\bigl(S, j\bigr), \operatorname{Stage.guard}\bigl(S, k\bigr), \mathit{aM}, \mathit{m0}, \mathit{m1}, \mathit{bm0}, \mathit{bm1}, p\bigr), \operatorname{Max.max}\bigl(\operatorname{ite}\bigl(\bigl(\operatorname{PairData.strongLower}\bigl(P, 0\bigr) < \operatorname{PairData.strongLower}\bigl(Q, 0\bigr)\bigr), \bigl(\bigl(\mathit{b1}+\bigl(\mathit{degree}\cdot \mathit{aD}\bigr)\bigr)+\mathit{dt}\bigr), 0\bigr), \operatorname{ite}\bigl(\bigl(\operatorname{Stage.guard}\bigl(S, k\bigr) < \operatorname{Stage.guard}\bigl(S, j\bigr)\bigr), \bigl(\bigl(\bigl(\mathit{b0}+\mathit{b1}\bigr)+\bigl(\bigl(\mathit{degree}-1\bigr)\cdot \mathit{aD}\bigr)\bigr)+\mathit{dg}\bigr), 0\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)
--   $$
--
--   Here $\mathbb B=\{\mathsf{false},\mathsf{true}\}$; $\mathcal P_{\mathrm{fin}}(X)$ denotes the finite subsets of $X$. Named functions and predicates refer to their definitions in the cited source. This result supplies the corresponding minmax strict D parent step in the verified $22$-level sensitivity construction.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; MinmaxDParent.lean, lines 41–96.

import Definitions.Def_Sensitivity213981Formal_ConditionalOrdinary
import Definitions.Def_Sensitivity213981Formal_MinmaxPairData
import Definitions.Def_Sensitivity213981Formal_MinmaxPairM
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_StrictUnion
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

theorem Sensitivity213981Formal.ThreeBoundMinmaxTransfer.minmax_strictD_parent :
∀ {L I V : Type} [inst : LinearOrder.{0} L] [inst_1 : Fintype.{0} I] [inst_2 : Fintype.{0} V]
  (S : Sensitivity213981Formal.ThreeBoundWitness.Stage L I V)
  (hT :
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
  (i j k l : L)
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
  (hjzero :
    @Eq.{1} Nat (@Sensitivity213981Formal.ThreeBoundWitness.Stage.tolerance L I V S j)
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (hlzero :
    @Eq.{1} Nat (@Sensitivity213981Formal.ThreeBoundWitness.Stage.tolerance L I V S l)
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (tl : L)
  (hldef :
    ∀ (u z : I → Bool),
      @Eq.{1} Bool
        (@Sensitivity213981Formal.ThreeBoundWitness.Stage.target L I V S l
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) u z)
        (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.mm L I F tl tl u z))
  (hujl :
    @LE.le.{0} L
      (@Preorder.toLE.{0} L
        (@PartialOrder.toPreorder.{0} L
          (@SemilatticeInf.toPartialOrder.{0} L
            (@Lattice.toSemilatticeInf.{0} L
              (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst))))))
      (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper L I V
        (@PartialOrder.toPreorder.{0} L
          (@SemilatticeInf.toPartialOrder.{0} L
            (@Lattice.toSemilatticeInf.{0} L
              (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
        S F i j P (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      tl)
  (hukl :
    @LE.le.{0} L
      (@Preorder.toLE.{0} L
        (@PartialOrder.toPreorder.{0} L
          (@SemilatticeInf.toPartialOrder.{0} L
            (@Lattice.toSemilatticeInf.{0} L
              (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst))))))
      (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper L I V
        (@PartialOrder.toPreorder.{0} L
          (@SemilatticeInf.toPartialOrder.{0} L
            (@Lattice.toSemilatticeInf.{0} L
              (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
        S F j k Q (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      tl)
  (hglgk :
    @LE.le.{0} L
      (@Preorder.toLE.{0} L
        (@PartialOrder.toPreorder.{0} L
          (@SemilatticeInf.toPartialOrder.{0} L
            (@Lattice.toSemilatticeInf.{0} L
              (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst))))))
      (@Sensitivity213981Formal.ThreeBoundWitness.Stage.guard L I V S l)
      (@Sensitivity213981Formal.ThreeBoundWitness.Stage.guard L I V S k))
  (degree aM m0 m1 bm0 bm1 p b0 b1 aD dt dg : Nat)
  (hd :
    ∀ (v : V),
      @Eq.{1} Nat (@Finset.card.{0} V (@Sensitivity213981Formal.ThreeBoundPositive.outgoing L I V inst_2 S v)) degree)
  (haM :
    @Sensitivity213981Formal.ThreeBoundProfiles.ABound L I inst_1 F
      (@Sensitivity213981Formal.ThreeBoundWitness.Stage.guard L I V S j)
      (@Sensitivity213981Formal.ThreeBoundWitness.Stage.guard L I V S i) aM)
  (hm0 :
    @Sensitivity213981Formal.ThreeBoundProfiles.MBound L I inst_1 F
      (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.weakLower L I V
        (@PartialOrder.toPreorder.{0} L
          (@SemilatticeInf.toPartialOrder.{0} L
            (@Lattice.toSemilatticeInf.{0} L
              (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
        S F i j P (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower L I V
        (@PartialOrder.toPreorder.{0} L
          (@SemilatticeInf.toPartialOrder.{0} L
            (@Lattice.toSemilatticeInf.{0} L
              (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
        S F i j P (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower L I V
        (@PartialOrder.toPreorder.{0} L
          (@SemilatticeInf.toPartialOrder.{0} L
            (@Lattice.toSemilatticeInf.{0} L
              (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
        S F j k Q (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      m0)
  (hm1 :
    @Sensitivity213981Formal.ThreeBoundProfiles.MBound L I inst_1 F
      (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.weakUpper L I V
        (@PartialOrder.toPreorder.{0} L
          (@SemilatticeInf.toPartialOrder.{0} L
            (@Lattice.toSemilatticeInf.{0} L
              (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
        S F i j P (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper L I V
        (@PartialOrder.toPreorder.{0} L
          (@SemilatticeInf.toPartialOrder.{0} L
            (@Lattice.toSemilatticeInf.{0} L
              (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
        S F i j P (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper L I V
        (@PartialOrder.toPreorder.{0} L
          (@SemilatticeInf.toPartialOrder.{0} L
            (@Lattice.toSemilatticeInf.{0} L
              (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
        S F j k Q (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      m1)
  (hbm0 :
    @Sensitivity213981Formal.ThreeBoundProfiles.BBound L I inst_1 F
      (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.weakLower L I V
        (@PartialOrder.toPreorder.{0} L
          (@SemilatticeInf.toPartialOrder.{0} L
            (@Lattice.toSemilatticeInf.{0} L
              (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
        S F i j P (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower L I V
        (@PartialOrder.toPreorder.{0} L
          (@SemilatticeInf.toPartialOrder.{0} L
            (@Lattice.toSemilatticeInf.{0} L
              (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
        S F j k Q (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      bm0)
  (hbm1 :
    @Sensitivity213981Formal.ThreeBoundProfiles.BBound L I inst_1 F
      (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.weakUpper L I V
        (@PartialOrder.toPreorder.{0} L
          (@SemilatticeInf.toPartialOrder.{0} L
            (@Lattice.toSemilatticeInf.{0} L
              (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
        S F i j P (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper L I V
        (@PartialOrder.toPreorder.{0} L
          (@SemilatticeInf.toPartialOrder.{0} L
            (@Lattice.toSemilatticeInf.{0} L
              (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
        S F j k Q (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      bm1)
  (hp :
    @Sensitivity213981Formal.ThreeBoundProfiles.PBound L I inst_1 F
      (@Sensitivity213981Formal.ThreeBoundWitness.Stage.guard L I V S k)
      (@Sensitivity213981Formal.ThreeBoundWitness.Stage.guard L I V S j)
      (@Sensitivity213981Formal.ThreeBoundWitness.Stage.guard L I V S i) p)
  (hb0 :
    @Sensitivity213981Formal.ThreeBoundProfiles.BBound L I inst_1 F
      (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.weakLower L I V
        (@PartialOrder.toPreorder.{0} L
          (@SemilatticeInf.toPartialOrder.{0} L
            (@Lattice.toSemilatticeInf.{0} L
              (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
        S F i j P (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      tl b0)
  (hb1 :
    @Sensitivity213981Formal.ThreeBoundProfiles.BBound L I inst_1 F
      (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.weakUpper L I V
        (@PartialOrder.toPreorder.{0} L
          (@SemilatticeInf.toPartialOrder.{0} L
            (@Lattice.toSemilatticeInf.{0} L
              (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
        S F i j P (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      tl b1)
  (haD :
    @Sensitivity213981Formal.ThreeBoundProfiles.ABound L I inst_1 F
      (@Sensitivity213981Formal.ThreeBoundWitness.Stage.guard L I V S l)
      (@Sensitivity213981Formal.ThreeBoundWitness.Stage.guard L I V S i) aD)
  (hdt :
    @Sensitivity213981Formal.ThreeBoundProfiles.DBound L I inst_1 F
      (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.weakLower L I V
        (@PartialOrder.toPreorder.{0} L
          (@SemilatticeInf.toPartialOrder.{0} L
            (@Lattice.toSemilatticeInf.{0} L
              (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
        S F i j P (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower L I V
        (@PartialOrder.toPreorder.{0} L
          (@SemilatticeInf.toPartialOrder.{0} L
            (@Lattice.toSemilatticeInf.{0} L
              (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
        S F i j P (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower L I V
        (@PartialOrder.toPreorder.{0} L
          (@SemilatticeInf.toPartialOrder.{0} L
            (@Lattice.toSemilatticeInf.{0} L
              (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
        S F j k Q (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      tl dt)
  (hdg :
    @Sensitivity213981Formal.ThreeBoundProfiles.DBound L I inst_1 F
      (@Sensitivity213981Formal.ThreeBoundWitness.Stage.guard L I V S l)
      (@Sensitivity213981Formal.ThreeBoundWitness.Stage.guard L I V S k)
      (@Sensitivity213981Formal.ThreeBoundWitness.Stage.guard L I V S j)
      (@Sensitivity213981Formal.ThreeBoundWitness.Stage.guard L I V S i) dg),
  @Sensitivity213981Formal.ThreeBoundProfiles.DBound L (Prod.{0, 0} (Prod.{0, 0} V Bool) I)
    (@instFintypeProd.{0, 0} (Prod.{0, 0} V Bool) I (@instFintypeProd.{0, 0} V Bool inst_2 Bool.fintype) inst_1)
    (@Sensitivity213981Formal.ThreeBoundWitness.parent L I V inst_2 S F) i j k l
    (@Max.max.{0} Nat Nat.instMax
      (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.pairMCost L inst degree
        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower L I V
          (@PartialOrder.toPreorder.{0} L
            (@SemilatticeInf.toPartialOrder.{0} L
              (@Lattice.toSemilatticeInf.{0} L
                (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
          S F i j P (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper L I V
          (@PartialOrder.toPreorder.{0} L
            (@SemilatticeInf.toPartialOrder.{0} L
              (@Lattice.toSemilatticeInf.{0} L
                (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
          S F i j P (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower L I V
          (@PartialOrder.toPreorder.{0} L
            (@SemilatticeInf.toPartialOrder.{0} L
              (@Lattice.toSemilatticeInf.{0} L
                (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
          S F j k Q (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper L I V
          (@PartialOrder.toPreorder.{0} L
            (@SemilatticeInf.toPartialOrder.{0} L
              (@Lattice.toSemilatticeInf.{0} L
                (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
          S F j k Q (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@Sensitivity213981Formal.ThreeBoundWitness.Stage.guard L I V S j)
        (@Sensitivity213981Formal.ThreeBoundWitness.Stage.guard L I V S k) aM m0 m1 bm0 bm1 p)
      (@Max.max.{0} Nat Nat.instMax
        (@ite.{1} Nat
          (@LT.lt.{0} L
            (@Preorder.toLT.{0} L
              (@PartialOrder.toPreorder.{0} L
                (@SemilatticeInf.toPartialOrder.{0} L
                  (@Lattice.toSemilatticeInf.{0} L
                    (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst))))))
            (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower L I V
              (@PartialOrder.toPreorder.{0} L
                (@SemilatticeInf.toPartialOrder.{0} L
                  (@Lattice.toSemilatticeInf.{0} L
                    (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
              S F i j P (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
            (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower L I V
              (@PartialOrder.toPreorder.{0} L
                (@SemilatticeInf.toPartialOrder.{0} L
                  (@Lattice.toSemilatticeInf.{0} L
                    (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
              S F j k Q (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
          (@LinearOrder.toDecidableLT.{0} L inst
            (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower L I V
              (@PartialOrder.toPreorder.{0} L
                (@SemilatticeInf.toPartialOrder.{0} L
                  (@Lattice.toSemilatticeInf.{0} L
                    (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
              S F i j P (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
            (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower L I V
              (@PartialOrder.toPreorder.{0} L
                (@SemilatticeInf.toPartialOrder.{0} L
                  (@Lattice.toSemilatticeInf.{0} L
                    (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
              S F j k Q (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) b1
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) degree aD))
            dt)
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@ite.{1} Nat
          (@LT.lt.{0} L
            (@Preorder.toLT.{0} L
              (@PartialOrder.toPreorder.{0} L
                (@SemilatticeInf.toPartialOrder.{0} L
                  (@Lattice.toSemilatticeInf.{0} L
                    (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst))))))
            (@Sensitivity213981Formal.ThreeBoundWitness.Stage.guard L I V S k)
            (@Sensitivity213981Formal.ThreeBoundWitness.Stage.guard L I V S j))
          (@LinearOrder.toDecidableLT.{0} L inst (@Sensitivity213981Formal.ThreeBoundWitness.Stage.guard L I V S k)
            (@Sensitivity213981Formal.ThreeBoundWitness.Stage.guard L I V S j))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) b0 b1)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) degree
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                aD))
            dg)
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))) := by sorry
