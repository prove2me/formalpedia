-- Prove2me | Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxTransfer_oriented_union_weighted
-- name    : Sensitivity213981Formal.ThreeBoundMinmaxTransfer.oriented_union_weighted
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-26T20:10:34.599269+00:00
-- url     : https://prove2.me/theorems/a9127c33-fa79-4581-9129-1b0df0d6346f
-- title:
--   oriented union weighted — Boolean sensitivity certificate
-- statement:
--   The following universally quantified assertion holds for the finite sets, Boolean families, tournament data, and profile coordinates defined in the imported interfaces. Each binder specifies the domain of its variable, and bracketed conditions specify finite or ordered structures.
--
--   $$
--   \forall L:\mathcal U,\quad \forall I:\mathcal U,\quad \forall V:\mathcal U,\quad \bigl[\operatorname{LinearOrder}\bigl(L\bigr)\bigr]\;\bigl[\mathrm{finite}(I)\bigr]\;\bigl[\mathrm{finite}(V)\bigr]\;\forall S:\operatorname{Witness.Stage}\bigl(L, I, V\bigr),\quad \forall F:\left(L\to \left(\left(I\to \mathbb B\right)\to \mathbb B\right)\right),\quad \bigl(\operatorname{Profiles.Nested}\bigl(F\bigr)\Longrightarrow \forall \mathit{ti}:L,\quad \forall \mathit{ui}:L,\quad \forall \mathit{gi}:L,\quad \forall x:\left(V\times \mathbb B\times I\to \mathbb B\right),\quad \forall v:V,\quad \forall c:\mathbb B,\quad \bigl(\operatorname{MinmaxTransfer.orientedRow}\bigl(S, F, \mathit{ti}, \mathit{ui}, \mathit{gi}, 0, x, v, c\bigr)\Longrightarrow \forall \mathit{Ulo}:\mathcal P_{\mathrm{fin}}(V\times \mathbb B\times I),\quad \forall \mathit{Uhi}:\mathcal P_{\mathrm{fin}}(V\times \mathbb B\times I),\quad \forall W:\left(V\to \mathcal P_{\mathrm{fin}}(V\times \mathbb B\times I)\right),\quad \forall E:\mathcal P_{\mathrm{fin}}(V\times \mathbb B\times I),\quad \bigl(\bigl(\operatorname{Positive.liftBits}\bigl(v, \operatorname{Bool.not}\bigl(c\bigr), \operatorname{Profiles.flipsTo}\bigl(F\bigl(\mathit{ti}\bigr), \mathsf{false}, \operatorname{Witness.child}\bigl(x, v, \operatorname{Bool.not}\bigl(c\bigr)\bigr)\bigr)\bigr) \le \mathit{Ulo}\bigr)\Longrightarrow \bigl(\bigl(\operatorname{Positive.liftBits}\bigl(v, c, \operatorname{Profiles.flipsTo}\bigl(F\bigl(\mathit{ui}\bigr), \mathsf{false}, \operatorname{Witness.child}\bigl(x, v, c\bigr)\bigr)\bigr) \le \mathit{Uhi}\bigr)\Longrightarrow \bigl(\forall w:V,\quad \bigl(w\in \operatorname{Positive.outgoing}\bigl(S, v\bigr)\Longrightarrow \bigl(\operatorname{Positive.liftBits}\bigl(w, \operatorname{Stage.label}\bigl(S, v, w\bigr), \operatorname{Profiles.flipsTo}\bigl(F\bigl(\mathit{gi}\bigr), \mathsf{true}, \operatorname{Witness.child}\bigl(x, w, \operatorname{Stage.label}\bigl(S, v, w\bigr)\bigr)\bigr)\bigr) \le W\bigl(w\bigr)\bigr)\bigr)\Longrightarrow \bigl(\bigl(E \le \operatorname{Union.union}\bigl(\operatorname{Union.union}\bigl(\mathit{Ulo}, \mathit{Uhi}\bigr), \operatorname{Finset.biUnion}\bigl(\operatorname{Positive.outgoing}\bigl(S, v\bigr), W\bigr)\bigr)\bigr)\Longrightarrow \forall \mathit{ulo}:\mathbb N,\quad \forall \mathit{uhi}:\mathbb N,\quad \forall z:\left(V\to \mathbb N\right),\quad \bigl(\bigl(|\mathit{Ulo}| \le \mathit{ulo}\bigr)\Longrightarrow \bigl(\bigl(|\mathit{Uhi}| \le \mathit{uhi}\bigr)\Longrightarrow \bigl(\forall w:V,\quad \bigl(w\in \operatorname{Positive.outgoing}\bigl(S, v\bigr)\Longrightarrow \bigl(|W\bigl(w\bigr)| \le z\bigl(w\bigr)\bigr)\bigr)\Longrightarrow \bigl(|\operatorname{Union.union}\bigl(\operatorname{Profiles.flipsTo}\bigl(\operatorname{MinmaxTransfer.orientedRowBool}\bigl(S, F, \mathit{ti}, \mathit{ui}, \mathit{gi}, 0, v, c\bigr), \mathsf{false}, x\bigr), E\bigr)| \le \bigl(\bigl(\mathit{ulo}+\mathit{uhi}\bigr)+\sum_{w\in \operatorname{Positive.outgoing}\bigl(S, v\bigr)} z\bigl(w\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)
--   $$
--
--   Here $\mathbb B=\{\mathsf{false},\mathsf{true}\}$; $\mathcal P_{\mathrm{fin}}(X)$ denotes the finite subsets of $X$. Named functions and predicates refer to their definitions in the cited source. This result supplies the corresponding oriented union weighted step in the verified $22$-level sensitivity construction.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; MinmaxUnionRows.lean, lines 55–88.

import Definitions.Def_Sensitivity213981Formal_ConditionalOrdinary
import Definitions.Def_Sensitivity213981Formal_MinmaxPairM
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_StrictUnion
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

theorem Sensitivity213981Formal.ThreeBoundMinmaxTransfer.oriented_union_weighted :
∀ {L I V : Type} [inst : LinearOrder.{0} L] [inst_1 : Fintype.{0} I] [inst_2 : Fintype.{0} V]
  (S : Sensitivity213981Formal.ThreeBoundWitness.Stage L I V) (F : L → (I → Bool) → Bool)
  (hF :
    @Sensitivity213981Formal.ThreeBoundProfiles.Nested L I
      (@PartialOrder.toPreorder.{0} L
        (@SemilatticeInf.toPartialOrder.{0} L
          (@Lattice.toSemilatticeInf.{0} L
            (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
      F)
  (ti ui gi : L) (x : Prod.{0, 0} (Prod.{0, 0} V Bool) I → Bool) (v : V) (c : Bool)
  (hv :
    @Sensitivity213981Formal.ThreeBoundMinmaxTransfer.orientedRow L I V inst_2 S F ti ui gi
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) x v c)
  (Ulo Uhi : Finset.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I)) (W : V → Finset.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I))
  (E : Finset.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I))
  (hlo :
    @LE.le.{0} (Finset.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I))
      (@Preorder.toLE.{0} (Finset.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I))
        (@PartialOrder.toPreorder.{0} (Finset.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I))
          (@Finset.instPartialOrder.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I))))
      (@Sensitivity213981Formal.ThreeBoundPositive.liftBits I V v (Bool.not c)
        (@Sensitivity213981Formal.ThreeBoundProfiles.flipsTo I inst_1 (F ti) Bool.false
          (@Sensitivity213981Formal.ThreeBoundWitness.child I V x v (Bool.not c))))
      Ulo)
  (hhi :
    @LE.le.{0} (Finset.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I))
      (@Preorder.toLE.{0} (Finset.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I))
        (@PartialOrder.toPreorder.{0} (Finset.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I))
          (@Finset.instPartialOrder.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I))))
      (@Sensitivity213981Formal.ThreeBoundPositive.liftBits I V v c
        (@Sensitivity213981Formal.ThreeBoundProfiles.flipsTo I inst_1 (F ui) Bool.false
          (@Sensitivity213981Formal.ThreeBoundWitness.child I V x v c)))
      Uhi)
  (hg :
    ∀ (w : V),
      @Membership.mem.{0, 0} V (Finset.{0} V)
          (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V))
          (@Sensitivity213981Formal.ThreeBoundPositive.outgoing L I V inst_2 S v) w →
        @LE.le.{0} (Finset.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I))
          (@Preorder.toLE.{0} (Finset.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I))
            (@PartialOrder.toPreorder.{0} (Finset.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I))
              (@Finset.instPartialOrder.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I))))
          (@Sensitivity213981Formal.ThreeBoundPositive.liftBits I V w
            (@Sensitivity213981Formal.ThreeBoundWitness.Stage.label L I V S v w)
            (@Sensitivity213981Formal.ThreeBoundProfiles.flipsTo I inst_1 (F gi) Bool.true
              (@Sensitivity213981Formal.ThreeBoundWitness.child I V x w
                (@Sensitivity213981Formal.ThreeBoundWitness.Stage.label L I V S v w))))
          (W w))
  (he :
    @LE.le.{0} (Finset.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I))
      (@Preorder.toLE.{0} (Finset.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I))
        (@PartialOrder.toPreorder.{0} (Finset.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I))
          (@Finset.instPartialOrder.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I))))
      E
      (@Union.union.{0} (Finset.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I))
        (@Finset.instUnion.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I) fun (a b : Prod.{0, 0} (Prod.{0, 0} V Bool) I) =>
          @instDecidableEqProd.{0, 0} (Prod.{0, 0} V Bool) I
            (fun (a b : Prod.{0, 0} V Bool) =>
              @instDecidableEqProd.{0, 0} V Bool (fun (a b : V) => Classical.propDecidable (@Eq.{1} V a b))
                instDecidableEqBool a b)
            (fun (a b : I) => Classical.propDecidable (@Eq.{1} I a b)) a b)
        (@Union.union.{0} (Finset.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I))
          (@Finset.instUnion.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I) fun (a b : Prod.{0, 0} (Prod.{0, 0} V Bool) I) =>
            @instDecidableEqProd.{0, 0} (Prod.{0, 0} V Bool) I
              (fun (a b : Prod.{0, 0} V Bool) =>
                @instDecidableEqProd.{0, 0} V Bool (fun (a b : V) => Classical.propDecidable (@Eq.{1} V a b))
                  instDecidableEqBool a b)
              (fun (a b : I) => Classical.propDecidable (@Eq.{1} I a b)) a b)
          Ulo Uhi)
        (@Finset.biUnion.{0, 0} V (Prod.{0, 0} (Prod.{0, 0} V Bool) I)
          (fun (a b : Prod.{0, 0} (Prod.{0, 0} V Bool) I) =>
            @instDecidableEqProd.{0, 0} (Prod.{0, 0} V Bool) I
              (fun (a b : Prod.{0, 0} V Bool) =>
                @instDecidableEqProd.{0, 0} V Bool (fun (a b : V) => Classical.propDecidable (@Eq.{1} V a b))
                  instDecidableEqBool a b)
              (fun (a b : I) => Classical.propDecidable (@Eq.{1} I a b)) a b)
          (@Sensitivity213981Formal.ThreeBoundPositive.outgoing L I V inst_2 S v) W)))
  (ulo uhi : Nat) (z : V → Nat)
  (hUlo : @LE.le.{0} Nat instLENat (@Finset.card.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I) Ulo) ulo)
  (hUhi : @LE.le.{0} Nat instLENat (@Finset.card.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I) Uhi) uhi)
  (hW :
    ∀ (w : V),
      @Membership.mem.{0, 0} V (Finset.{0} V)
          (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V))
          (@Sensitivity213981Formal.ThreeBoundPositive.outgoing L I V inst_2 S v) w →
        @LE.le.{0} Nat instLENat (@Finset.card.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I) (W w)) (z w)),
  @LE.le.{0} Nat instLENat
    (@Finset.card.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I)
      (@Union.union.{0} (Finset.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I))
        (@Finset.instUnion.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I) fun (a b : Prod.{0, 0} (Prod.{0, 0} V Bool) I) =>
          @instDecidableEqProd.{0, 0} (Prod.{0, 0} V Bool) I
            (fun (a b : Prod.{0, 0} V Bool) =>
              @instDecidableEqProd.{0, 0} V Bool (fun (a b : V) => Classical.propDecidable (@Eq.{1} V a b))
                instDecidableEqBool a b)
            (fun (a b : I) => Classical.propDecidable (@Eq.{1} I a b)) a b)
        (@Sensitivity213981Formal.ThreeBoundProfiles.flipsTo (Prod.{0, 0} (Prod.{0, 0} V Bool) I)
          (@instFintypeProd.{0, 0} (Prod.{0, 0} V Bool) I (@instFintypeProd.{0, 0} V Bool inst_2 Bool.fintype) inst_1)
          (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.orientedRowBool L I V inst_2 S F ti ui gi
            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) v c)
          Bool.false x)
        E))
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) ulo uhi)
      (@Finset.sum.{0, 0} V Nat Nat.instAddCommMonoid
        (@Sensitivity213981Formal.ThreeBoundPositive.outgoing L I V inst_2 S v) fun (w : V) => z w)) := by sorry
