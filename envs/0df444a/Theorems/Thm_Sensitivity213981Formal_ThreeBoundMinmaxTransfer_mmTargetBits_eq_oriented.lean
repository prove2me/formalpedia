-- Prove2me | Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxTransfer_mmTargetBits_eq_oriented
-- name    : Sensitivity213981Formal.ThreeBoundMinmaxTransfer.mmTargetBits_eq_oriented
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-26T20:07:48.798949+00:00
-- url     : https://prove2.me/theorems/542256fd-ce04-4908-8748-751a0cdd2a7e
-- title:
--   mm Target Bits eq oriented — Boolean sensitivity certificate
-- statement:
--   The following universally quantified assertion holds for the finite sets, Boolean families, tournament data, and profile coordinates defined in the imported interfaces. Each binder specifies the domain of its variable, and bracketed conditions specify finite or ordered structures.
--
--   $$
--   \forall L:\mathcal U,\quad \forall I:\mathcal U,\quad \forall V:\mathcal U,\quad \bigl[\operatorname{LinearOrder}\bigl(L\bigr)\bigr]\;\bigl[\mathrm{finite}(I)\bigr]\;\bigl[\mathrm{finite}(V)\bigr]\;\forall F:\left(L\to \left(\left(I\to \mathbb B\right)\to \mathbb B\right)\right),\quad \bigl(\operatorname{Profiles.Nested}\bigl(F\bigr)\Longrightarrow \forall t:L,\quad \forall u:L,\quad \bigl(\bigl(t \le u\bigr)\Longrightarrow \forall x:\left(V\times \mathbb B\times I\to \mathbb B\right),\quad \forall w:V,\quad \forall c:\mathbb B,\quad \bigl(\bigl(F\bigl(u, \operatorname{Witness.child}\bigl(x, w, c\bigr)\bigr) = \mathsf{true}\bigr)\Longrightarrow \bigl(\bigl(F\bigl(t, \operatorname{Witness.child}\bigl(x, w, \operatorname{Bool.not}\bigl(c\bigr)\bigr)\bigr) = \mathsf{true}\bigr)\Longrightarrow \bigl(\operatorname{MinmaxTransfer.mmTargetBits}\bigl(F, t, u, x, w\bigr) = \operatorname{ite}\bigl(\bigl(F\bigl(u, \operatorname{Witness.child}\bigl(x, w, \operatorname{Bool.not}\bigl(c\bigr)\bigr)\bigr) = \mathsf{true}\bigr), \operatorname{MinmaxTransfer.orientedBits}\bigl(F, t, t, x, w, c\bigr), \operatorname{MinmaxTransfer.orientedBits}\bigl(F, t, u, x, w, c\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)
--   $$
--
--   Here $\mathbb B=\{\mathsf{false},\mathsf{true}\}$; $\mathcal P_{\mathrm{fin}}(X)$ denotes the finite subsets of $X$. Named functions and predicates refer to their definitions in the cited source. This result supplies the corresponding mm Target Bits eq oriented step in the verified $22$-level sensitivity construction.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; MinmaxB.lean, lines 50–77.

import Definitions.Def_Sensitivity213981Formal_MinmaxB
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

theorem Sensitivity213981Formal.ThreeBoundMinmaxTransfer.mmTargetBits_eq_oriented :
∀ {L I V : Type} [inst : LinearOrder.{0} L] [inst_1 : Fintype.{0} I] [Fintype.{0} V] (F : L → (I → Bool) → Bool)
  (hF :
    @Sensitivity213981Formal.ThreeBoundProfiles.Nested L I
      (@PartialOrder.toPreorder.{0} L
        (@SemilatticeInf.toPartialOrder.{0} L
          (@Lattice.toSemilatticeInf.{0} L
            (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
      F)
  (t u : L)
  (htu :
    @LE.le.{0} L
      (@Preorder.toLE.{0} L
        (@PartialOrder.toPreorder.{0} L
          (@SemilatticeInf.toPartialOrder.{0} L
            (@Lattice.toSemilatticeInf.{0} L
              (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst))))))
      t u)
  (x : Prod.{0, 0} (Prod.{0, 0} V Bool) I → Bool) (w : V) (c : Bool)
  (hh : @Eq.{1} Bool (F u (@Sensitivity213981Formal.ThreeBoundWitness.child I V x w c)) Bool.true)
  (hl : @Eq.{1} Bool (F t (@Sensitivity213981Formal.ThreeBoundWitness.child I V x w (Bool.not c))) Bool.true),
  @Eq.{1} (Finset.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I))
    (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.mmTargetBits L I V inst_1 F t u x w)
    (@ite.{1} (Finset.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I))
      (@Eq.{1} Bool (F u (@Sensitivity213981Formal.ThreeBoundWitness.child I V x w (Bool.not c))) Bool.true)
      (instDecidableEqBool (F u (@Sensitivity213981Formal.ThreeBoundWitness.child I V x w (Bool.not c))) Bool.true)
      (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.orientedBits L I V inst_1 F t t x w c)
      (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.orientedBits L I V inst_1 F t u x w c)) := by sorry
