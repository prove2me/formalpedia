-- Prove2me | Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxTransfer_oriented_union_guard_bound
-- name    : Sensitivity213981Formal.ThreeBoundMinmaxTransfer.oriented_union_guard_bound
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-26T20:17:46.404071+00:00
-- url     : https://prove2.me/theorems/3cf0ace4-f1f6-4c68-aece-766168390675
-- title:
--   oriented union guard bound — Boolean sensitivity certificate
-- statement:
--   The following universally quantified assertion holds for the finite sets, Boolean families, tournament data, and profile coordinates defined in the imported interfaces. Each binder specifies the domain of its variable, and bracketed conditions specify finite or ordered structures.
--
--   $$
--   \forall L:\mathcal U,\quad \forall I:\mathcal U,\quad \forall V:\mathcal U,\quad \bigl[\operatorname{LinearOrder}\bigl(L\bigr)\bigr]\;\bigl[\mathrm{finite}(I)\bigr]\;\bigl[\mathrm{finite}(V)\bigr]\;\forall S:\operatorname{Witness.Stage}\bigl(L, I, V\bigr),\quad \forall F:\left(L\to \left(\left(I\to \mathbb B\right)\to \mathbb B\right)\right),\quad \bigl(\operatorname{Profiles.Nested}\bigl(F\bigr)\Longrightarrow \forall \mathit{ti}:L,\quad \forall \mathit{ui}:L,\quad \forall \mathit{tl}:L,\quad \forall \mathit{gi}:L,\quad \forall \mathit{gl}:L,\quad \forall \mathit{degree}:\mathbb N,\quad \forall \mathit{b0}:\mathbb N,\quad \forall \mathit{b1}:\mathbb N,\quad \forall a:\mathbb N,\quad \forall u:\mathbb N,\quad \bigl(\operatorname{Profiles.BBound}\bigl(F, \mathit{ti}, \mathit{tl}, \mathit{b0}\bigr)\Longrightarrow \bigl(\operatorname{Profiles.BBound}\bigl(F, \mathit{ui}, \mathit{tl}, \mathit{b1}\bigr)\Longrightarrow \bigl(\operatorname{Profiles.ABound}\bigl(F, \mathit{gl}, \mathit{gi}, a\bigr)\Longrightarrow \forall x:\left(V\times \mathbb B\times I\to \mathbb B\right),\quad \forall v:V,\quad \forall \mathit{w₀}:V,\quad \forall c:\mathbb B,\quad \bigl(\bigl(|\operatorname{Positive.outgoing}\bigl(S, v\bigr)| = \mathit{degree}\bigr)\Longrightarrow \bigl(\operatorname{MinmaxTransfer.orientedRow}\bigl(S, F, \mathit{ti}, \mathit{ui}, \mathit{gi}, 0, x, v, c\bigr)\Longrightarrow \bigl(\forall e:\mathbb B,\quad \bigl(F\bigl(\mathit{tl}, \operatorname{Witness.child}\bigl(x, v, e\bigr)\bigr) = \mathsf{true}\bigr)\Longrightarrow \bigl(\bigl(\operatorname{Conditional.guardFailures}\bigl(S, F, \mathit{gl}, x, v\bigr) = \operatorname{Singleton.singleton}\bigl(\mathit{w₀}\bigr)\bigr)\Longrightarrow \bigl(\bigl(|\operatorname{Union.union}\bigl(\operatorname{Profiles.flipsTo}\bigl(F\bigl(\mathit{gi}\bigr), \mathsf{true}, \operatorname{Witness.child}\bigl(x, \mathit{w₀}, \operatorname{Stage.label}\bigl(S, v, \mathit{w₀}\bigr)\bigr)\bigr), \operatorname{Profiles.flipsTo}\bigl(F\bigl(\mathit{gl}\bigr), \mathsf{false}, \operatorname{Witness.child}\bigl(x, \mathit{w₀}, \operatorname{Stage.label}\bigl(S, v, \mathit{w₀}\bigr)\bigr)\bigr)\bigr)| \le u\bigr)\Longrightarrow \bigl(|\operatorname{Union.union}\bigl(\operatorname{Profiles.flipsTo}\bigl(\operatorname{MinmaxTransfer.orientedRowBool}\bigl(S, F, \mathit{ti}, \mathit{ui}, \mathit{gi}, 0, v, c\bigr), \mathsf{false}, x\bigr), \operatorname{Profiles.flipsTo}\bigl(\operatorname{Conditional.ordinaryRowBool}\bigl(S, F, \mathit{tl}, \mathit{gl}, 0, v\bigr), \mathsf{true}, x\bigr)\bigr)| \le \bigl(\bigl(\bigl(\mathit{b0}+\mathit{b1}\bigr)+\bigl(\bigl(\mathit{degree}-1\bigr)\cdot a\bigr)\bigr)+u\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)
--   $$
--
--   Here $\mathbb B=\{\mathsf{false},\mathsf{true}\}$; $\mathcal P_{\mathrm{fin}}(X)$ denotes the finite subsets of $X$. Named functions and predicates refer to their definitions in the cited source. This result supplies the corresponding oriented union guard bound step in the verified $22$-level sensitivity construction.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; MinmaxUnionRows.lean, lines 133–181.

import Definitions.Def_Sensitivity213981Formal_ConditionalOrdinary
import Definitions.Def_Sensitivity213981Formal_MinmaxPairM
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_StrictUnion
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

theorem Sensitivity213981Formal.ThreeBoundMinmaxTransfer.oriented_union_guard_bound :
∀ {L I V : Type} [inst : LinearOrder.{0} L] [inst_1 : Fintype.{0} I] [inst_2 : Fintype.{0} V]
  (S : Sensitivity213981Formal.ThreeBoundWitness.Stage L I V) (F : L → (I → Bool) → Bool)
  (hF :
    @Sensitivity213981Formal.ThreeBoundProfiles.Nested L I
      (@PartialOrder.toPreorder.{0} L
        (@SemilatticeInf.toPartialOrder.{0} L
          (@Lattice.toSemilatticeInf.{0} L
            (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
      F)
  (ti ui tl gi gl : L) (degree b0 b1 a u : Nat)
  (hb0 : @Sensitivity213981Formal.ThreeBoundProfiles.BBound L I inst_1 F ti tl b0)
  (hb1 : @Sensitivity213981Formal.ThreeBoundProfiles.BBound L I inst_1 F ui tl b1)
  (ha : @Sensitivity213981Formal.ThreeBoundProfiles.ABound L I inst_1 F gl gi a)
  (x : Prod.{0, 0} (Prod.{0, 0} V Bool) I → Bool) (v w₀ : V) (c : Bool)
  (hd : @Eq.{1} Nat (@Finset.card.{0} V (@Sensitivity213981Formal.ThreeBoundPositive.outgoing L I V inst_2 S v)) degree)
  (hvi :
    @Sensitivity213981Formal.ThreeBoundMinmaxTransfer.orientedRow L I V inst_2 S F ti ui gi
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) x v c)
  (ht : ∀ (e : Bool), @Eq.{1} Bool (F tl (@Sensitivity213981Formal.ThreeBoundWitness.child I V x v e)) Bool.true)
  (hgl :
    @Eq.{1} (Finset.{0} V) (@Sensitivity213981Formal.ThreeBoundConditional.guardFailures L I V inst_2 S F gl x v)
      (@Singleton.singleton.{0, 0} V (Finset.{0} V) (@Finset.instSingleton.{0} V) w₀))
  (hu :
    @LE.le.{0} Nat instLENat
      (@Finset.card.{0} I
        (@Union.union.{0} (Finset.{0} I)
          (@Finset.instUnion.{0} I fun (a b : I) => Classical.propDecidable (@Eq.{1} I a b))
          (@Sensitivity213981Formal.ThreeBoundProfiles.flipsTo I inst_1 (F gi) Bool.true
            (@Sensitivity213981Formal.ThreeBoundWitness.child I V x w₀
              (@Sensitivity213981Formal.ThreeBoundWitness.Stage.label L I V S v w₀)))
          (@Sensitivity213981Formal.ThreeBoundProfiles.flipsTo I inst_1 (F gl) Bool.false
            (@Sensitivity213981Formal.ThreeBoundWitness.child I V x w₀
              (@Sensitivity213981Formal.ThreeBoundWitness.Stage.label L I V S v w₀)))))
      u),
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
        (@Sensitivity213981Formal.ThreeBoundProfiles.flipsTo (Prod.{0, 0} (Prod.{0, 0} V Bool) I)
          (@instFintypeProd.{0, 0} (Prod.{0, 0} V Bool) I (@instFintypeProd.{0, 0} V Bool inst_2 Bool.fintype) inst_1)
          (@Sensitivity213981Formal.ThreeBoundConditional.ordinaryRowBool L I V inst_2 S F tl gl
            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) v)
          Bool.true x)))
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) b0 b1)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) degree
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          a))
      u) := by sorry
