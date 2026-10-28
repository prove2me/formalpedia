-- Prove2me | Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxTransfer_oriented_pairM_row
-- name    : Sensitivity213981Formal.ThreeBoundMinmaxTransfer.oriented_pairM_row
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-26T20:10:29.620981+00:00
-- url     : https://prove2.me/theorems/42aa9d22-e023-4267-a47d-8146d16a4d5c
-- title:
--   oriented pair M row — Boolean sensitivity certificate
-- statement:
--   The following universally quantified assertion holds for the finite sets, Boolean families, tournament data, and profile coordinates defined in the imported interfaces. Each binder specifies the domain of its variable, and bracketed conditions specify finite or ordered structures.
--
--   $$
--   \forall L:\mathcal U,\quad \forall I:\mathcal U,\quad \forall V:\mathcal U,\quad \bigl[\operatorname{LinearOrder}\bigl(L\bigr)\bigr]\;\bigl[\mathrm{finite}(I)\bigr]\;\bigl[\mathrm{finite}(V)\bigr]\;\forall S:\operatorname{Witness.Stage}\bigl(L, I, V\bigr),\quad \forall F:\left(L\to \left(\left(I\to \mathbb B\right)\to \mathbb B\right)\right),\quad \bigl(\operatorname{Profiles.Nested}\bigl(F\bigr)\Longrightarrow \forall \mathit{ti}:L,\quad \forall \mathit{ui}:L,\quad \forall \mathit{tj}:L,\quad \forall \mathit{uj}:L,\quad \forall \mathit{tk}:L,\quad \forall \mathit{uk}:L,\quad \forall \mathit{gi}:L,\quad \forall \mathit{gj}:L,\quad \forall \mathit{gk}:L,\quad \bigl(\bigl(\mathit{ti} \le \mathit{tj}\bigr)\Longrightarrow \bigl(\bigl(\mathit{ui} \le \mathit{uj}\bigr)\Longrightarrow \bigl(\bigl(\mathit{gj} \le \mathit{gi}\bigr)\Longrightarrow \bigl(\bigl(\mathit{gk} \le \mathit{gj}\bigr)\Longrightarrow \forall q:\mathbb N,\quad \forall \mathit{degree}:\mathbb N,\quad \forall x:\left(V\times \mathbb B\times I\to \mathbb B\right),\quad \forall v:V,\quad \forall c:\mathbb B,\quad \bigl(\operatorname{MinmaxTransfer.orientedRow}\bigl(S, F, \mathit{tj}, \mathit{uj}, \mathit{gj}, q, x, v, c\bigr)\Longrightarrow \bigl(\bigl(|\operatorname{Conditional.guardFailures}\bigl(S, F, \mathit{gj}, x, v\bigr)| = q\bigr)\Longrightarrow \bigl(\neg \operatorname{MinmaxTransfer.orientedRow}\bigl(S, F, \mathit{tk}, \mathit{uk}, \mathit{gk}, q, x, v, c\bigr)\Longrightarrow \bigl(\bigl(|\operatorname{Positive.outgoing}\bigl(S, v\bigr)| = \mathit{degree}\bigr)\Longrightarrow \forall a:\mathbb N,\quad \forall \mathit{m0}:\mathbb N,\quad \forall \mathit{m1}:\mathbb N,\quad \forall \mathit{b0}:\mathbb N,\quad \forall \mathit{b1}:\mathbb N,\quad \forall p:\mathbb N,\quad \bigl(\operatorname{Profiles.ABound}\bigl(F, \mathit{gj}, \mathit{gi}, a\bigr)\Longrightarrow \bigl(\operatorname{Profiles.MBound}\bigl(F, \mathit{ti}, \mathit{tj}, \mathit{tk}, \mathit{m0}\bigr)\Longrightarrow \bigl(\operatorname{Profiles.MBound}\bigl(F, \mathit{ui}, \mathit{uj}, \mathit{uk}, \mathit{m1}\bigr)\Longrightarrow \bigl(\operatorname{Profiles.BBound}\bigl(F, \mathit{ti}, \mathit{tk}, \mathit{b0}\bigr)\Longrightarrow \bigl(\operatorname{Profiles.BBound}\bigl(F, \mathit{ui}, \mathit{uk}, \mathit{b1}\bigr)\Longrightarrow \bigl(\operatorname{Profiles.PBound}\bigl(F, \mathit{gk}, \mathit{gj}, \mathit{gi}, p\bigr)\Longrightarrow \bigl(|\operatorname{Profiles.flipsTo}\bigl(\operatorname{MinmaxTransfer.orientedRowBool}\bigl(S, F, \mathit{ti}, \mathit{ui}, \mathit{gi}, q, v, c\bigr), \mathsf{false}, x\bigr)| \le \operatorname{MinmaxTransfer.pairMCost}\bigl(\mathit{degree}, q, \mathit{tj}, \mathit{uj}, \mathit{tk}, \mathit{uk}, \mathit{gj}, \mathit{gk}, a, \mathit{m0}, \mathit{m1}, \mathit{b0}, \mathit{b1}, p\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)
--   $$
--
--   Here $\mathbb B=\{\mathsf{false},\mathsf{true}\}$; $\mathcal P_{\mathrm{fin}}(X)$ denotes the finite subsets of $X$. Named functions and predicates refer to their definitions in the cited source. This result supplies the corresponding oriented pair M row step in the verified $22$-level sensitivity construction.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; MinmaxPairM.lean, lines 165–226.

import Definitions.Def_Sensitivity213981Formal_ConditionalOrdinary
import Definitions.Def_Sensitivity213981Formal_MinmaxB
import Definitions.Def_Sensitivity213981Formal_MinmaxPairM
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_Supplement_GradedPositiveBoundary
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

theorem Sensitivity213981Formal.ThreeBoundMinmaxTransfer.oriented_pairM_row :
∀ {L I V : Type} [inst : LinearOrder.{0} L] [inst_1 : Fintype.{0} I] [inst_2 : Fintype.{0} V]
  (S : Sensitivity213981Formal.ThreeBoundWitness.Stage L I V) (F : L → (I → Bool) → Bool)
  (hF :
    @Sensitivity213981Formal.ThreeBoundProfiles.Nested L I
      (@PartialOrder.toPreorder.{0} L
        (@SemilatticeInf.toPartialOrder.{0} L
          (@Lattice.toSemilatticeInf.{0} L
            (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
      F)
  (ti ui tj uj tk uk gi gj gk : L)
  (htij :
    @LE.le.{0} L
      (@Preorder.toLE.{0} L
        (@PartialOrder.toPreorder.{0} L
          (@SemilatticeInf.toPartialOrder.{0} L
            (@Lattice.toSemilatticeInf.{0} L
              (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst))))))
      ti tj)
  (huij :
    @LE.le.{0} L
      (@Preorder.toLE.{0} L
        (@PartialOrder.toPreorder.{0} L
          (@SemilatticeInf.toPartialOrder.{0} L
            (@Lattice.toSemilatticeInf.{0} L
              (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst))))))
      ui uj)
  (hgij :
    @LE.le.{0} L
      (@Preorder.toLE.{0} L
        (@PartialOrder.toPreorder.{0} L
          (@SemilatticeInf.toPartialOrder.{0} L
            (@Lattice.toSemilatticeInf.{0} L
              (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst))))))
      gj gi)
  (hgkj :
    @LE.le.{0} L
      (@Preorder.toLE.{0} L
        (@PartialOrder.toPreorder.{0} L
          (@SemilatticeInf.toPartialOrder.{0} L
            (@Lattice.toSemilatticeInf.{0} L
              (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst))))))
      gk gj)
  (q degree : Nat) (x : Prod.{0, 0} (Prod.{0, 0} V Bool) I → Bool) (v : V) (c : Bool)
  (hj : @Sensitivity213981Formal.ThreeBoundMinmaxTransfer.orientedRow L I V inst_2 S F tj uj gj q x v c)
  (hcount :
    @Eq.{1} Nat
      (@Finset.card.{0} V (@Sensitivity213981Formal.ThreeBoundConditional.guardFailures L I V inst_2 S F gj x v)) q)
  (hk : Not (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.orientedRow L I V inst_2 S F tk uk gk q x v c))
  (hd : @Eq.{1} Nat (@Finset.card.{0} V (@Sensitivity213981Formal.ThreeBoundPositive.outgoing L I V inst_2 S v)) degree)
  (a m0 m1 b0 b1 p : Nat) (ha : @Sensitivity213981Formal.ThreeBoundProfiles.ABound L I inst_1 F gj gi a)
  (hm0 : @Sensitivity213981Formal.ThreeBoundProfiles.MBound L I inst_1 F ti tj tk m0)
  (hm1 : @Sensitivity213981Formal.ThreeBoundProfiles.MBound L I inst_1 F ui uj uk m1)
  (hb0 : @Sensitivity213981Formal.ThreeBoundProfiles.BBound L I inst_1 F ti tk b0)
  (hb1 : @Sensitivity213981Formal.ThreeBoundProfiles.BBound L I inst_1 F ui uk b1)
  (hp : @Sensitivity213981Formal.ThreeBoundProfiles.PBound L I inst_1 F gk gj gi p),
  @LE.le.{0} Nat instLENat
    (@Finset.card.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I)
      (@Sensitivity213981Formal.ThreeBoundProfiles.flipsTo (Prod.{0, 0} (Prod.{0, 0} V Bool) I)
        (@instFintypeProd.{0, 0} (Prod.{0, 0} V Bool) I (@instFintypeProd.{0, 0} V Bool inst_2 Bool.fintype) inst_1)
        (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.orientedRowBool L I V inst_2 S F ti ui gi q v c) Bool.false
        x))
    (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.pairMCost L inst degree q tj uj tk uk gj gk a m0 m1 b0 b1 p) := by sorry
