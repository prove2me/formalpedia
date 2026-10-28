-- Prove2me | Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxTransfer_oriented_zero_union_of_boundary
-- name    : Sensitivity213981Formal.ThreeBoundMinmaxTransfer.oriented_zero_union_of_boundary
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-26T20:25:51.821186+00:00
-- url     : https://prove2.me/theorems/51b01776-dc48-4880-bb75-159d000c8f58
-- title:
--   oriented zero union of boundary — Boolean sensitivity certificate
-- statement:
--   The following universally quantified assertion holds for the finite sets, Boolean families, tournament data, and profile coordinates defined in the imported interfaces. Each binder specifies the domain of its variable, and bracketed conditions specify finite or ordered structures.
--
--   $$
--   \forall L:\mathcal U,\quad \forall I:\mathcal U,\quad \forall V:\mathcal U,\quad \bigl[\operatorname{LinearOrder}\bigl(L\bigr)\bigr]\;\bigl[\mathrm{finite}(I)\bigr]\;\bigl[\mathrm{finite}(V)\bigr]\;\forall S:\operatorname{Witness.Stage}\bigl(L, I, V\bigr),\quad \bigl(\operatorname{TournamentHighRows.IsTournament}\bigl(\operatorname{Stage.Adj}\bigl(S\bigr)\bigr)\Longrightarrow \forall F:\left(L\to \left(\left(I\to \mathbb B\right)\to \mathbb B\right)\right),\quad \bigl(\operatorname{Profiles.Nested}\bigl(F\bigr)\Longrightarrow \forall G:\left(\left(V\times \mathbb B\times I\to \mathbb B\right)\to \mathbb B\right),\quad \forall \mathit{ti}:L,\quad \forall \mathit{ui}:L,\quad \forall \mathit{tj}:L,\quad \forall \mathit{uj}:L,\quad \forall \mathit{tk}:L,\quad \forall \mathit{uk}:L,\quad \forall \mathit{tl}:L,\quad \forall \mathit{gi}:L,\quad \forall \mathit{gj}:L,\quad \forall \mathit{gk}:L,\quad \forall \mathit{gl}:L,\quad \bigl(\bigl(\mathit{ti} \le \mathit{ui}\bigr)\Longrightarrow \bigl(\bigl(\mathit{ti} \le \mathit{tj}\bigr)\Longrightarrow \bigl(\bigl(\mathit{ui} \le \mathit{uj}\bigr)\Longrightarrow \bigl(\bigl(\mathit{uj} \le \mathit{tl}\bigr)\Longrightarrow \bigl(\bigl(\mathit{tk} \le \mathit{tl}\bigr)\Longrightarrow \bigl(\bigl(\mathit{uk} \le \mathit{tl}\bigr)\Longrightarrow \bigl(\bigl(\mathit{gj} \le \mathit{gi}\bigr)\Longrightarrow \bigl(\bigl(\mathit{gk} \le \mathit{gj}\bigr)\Longrightarrow \bigl(\bigl(\mathit{gl} \le \mathit{gk}\bigr)\Longrightarrow \bigl(\bigl(\mathit{gi} \le \mathit{tl}\bigr)\Longrightarrow \bigl(\bigl(\mathit{gl} \le \mathit{ti}\bigr)\Longrightarrow \forall \mathit{degree}:\mathbb N,\quad \forall \mathit{b0}:\mathbb N,\quad \forall \mathit{b1}:\mathbb N,\quad \forall a:\mathbb N,\quad \forall \mathit{dt}:\mathbb N,\quad \forall \mathit{dg}:\mathbb N,\quad \forall R:\mathbb N,\quad \bigl(\operatorname{Profiles.BBound}\bigl(F, \mathit{ti}, \mathit{tl}, \mathit{b0}\bigr)\Longrightarrow \bigl(\operatorname{Profiles.BBound}\bigl(F, \mathit{ui}, \mathit{tl}, \mathit{b1}\bigr)\Longrightarrow \bigl(\operatorname{Profiles.ABound}\bigl(F, \mathit{gl}, \mathit{gi}, a\bigr)\Longrightarrow \bigl(\operatorname{Profiles.DBound}\bigl(F, \mathit{ti}, \mathit{tj}, \mathit{tk}, \mathit{tl}, \mathit{dt}\bigr)\Longrightarrow \bigl(\operatorname{Profiles.DBound}\bigl(F, \mathit{gl}, \mathit{gk}, \mathit{gj}, \mathit{gi}, \mathit{dg}\bigr)\Longrightarrow \forall x:\left(V\times \mathbb B\times I\to \mathbb B\right),\quad \forall v:V,\quad \bigl(\bigl(|\operatorname{Positive.outgoing}\bigl(S, v\bigr)| = \mathit{degree}\bigr)\Longrightarrow \bigl(\bigl(\operatorname{MinmaxTransfer.mm}\bigl(F, \mathit{tj}, \mathit{uj}, \operatorname{Witness.child}\bigl(x, v, \mathsf{false}\bigr), \operatorname{Witness.child}\bigl(x, v, \mathsf{true}\bigr)\bigr) = \mathsf{true}\bigr)\Longrightarrow \bigl(\bigl(|\operatorname{Conditional.guardFailures}\bigl(S, F, \mathit{gj}, x, v\bigr)| = 0\bigr)\Longrightarrow \bigl(\forall c:\mathbb B,\quad \neg \operatorname{MinmaxTransfer.orientedRow}\bigl(S, F, \mathit{tk}, \mathit{uk}, \mathit{gk}, 0, x, v, c\bigr)\Longrightarrow \bigl(\forall c:\mathbb B,\quad \forall y:\left(V\times \mathbb B\times I\to \mathbb B\right),\quad \bigl(\operatorname{MinmaxTransfer.orientedRow}\bigl(S, F, \mathit{ti}, \mathit{ui}, \mathit{gi}, 0, y, v, c\bigr)\Longrightarrow \bigl(G\bigl(y\bigr) = \mathsf{true}\bigr)\bigr)\Longrightarrow \bigl(\forall c:\mathbb B,\quad \bigl(\operatorname{MinmaxTransfer.orientedRow}\bigl(S, F, \mathit{tj}, \mathit{uj}, \mathit{gj}, 0, x, v, c\bigr)\Longrightarrow \bigl(|\operatorname{Profiles.flipsTo}\bigl(\operatorname{MinmaxTransfer.orientedRowBool}\bigl(S, F, \mathit{ti}, \mathit{ui}, \mathit{gi}, 0, v, c\bigr), \mathsf{false}, x\bigr)| \le R\bigr)\bigr)\Longrightarrow \bigl(|\operatorname{Union.union}\bigl(\operatorname{Profiles.flipsTo}\bigl(G, \mathsf{false}, x\bigr), \operatorname{Profiles.flipsTo}\bigl(\operatorname{Conditional.ordinaryParent}\bigl(S, F, \mathit{tl}, \mathit{gl}, 0\bigr), \mathsf{true}, x\bigr)\bigr)| \le \operatorname{Max.max}\bigl(R, \operatorname{Max.max}\bigl(\operatorname{ite}\bigl(\bigl(\mathit{tj} < \mathit{tk}\bigr), \bigl(\bigl(\mathit{b1}+\bigl(\mathit{degree}\cdot a\bigr)\bigr)+\mathit{dt}\bigr), 0\bigr), \operatorname{ite}\bigl(\bigl(\mathit{gk} < \mathit{gj}\bigr), \bigl(\bigl(\bigl(\mathit{b0}+\mathit{b1}\bigr)+\bigl(\bigl(\mathit{degree}-1\bigr)\cdot a\bigr)\bigr)+\mathit{dg}\bigr), 0\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)
--   $$
--
--   Here $\mathbb B=\{\mathsf{false},\mathsf{true}\}$; $\mathcal P_{\mathrm{fin}}(X)$ denotes the finite subsets of $X$. Named functions and predicates refer to their definitions in the cited source. This result supplies the corresponding oriented zero union of boundary step in the verified $22$-level sensitivity construction.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; MinmaxStrictUnion.lean, lines 16–120.

import Definitions.Def_Sensitivity213981Formal_ConditionalOrdinary
import Definitions.Def_Sensitivity213981Formal_MinmaxPairData
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

theorem Sensitivity213981Formal.ThreeBoundMinmaxTransfer.oriented_zero_union_of_boundary :
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
  (G : (Prod.{0, 0} (Prod.{0, 0} V Bool) I → Bool) → Bool) (ti ui tj uj tk uk tl gi gj gk gl : L)
  (htiu :
    @LE.le.{0} L
      (@Preorder.toLE.{0} L
        (@PartialOrder.toPreorder.{0} L
          (@SemilatticeInf.toPartialOrder.{0} L
            (@Lattice.toSemilatticeInf.{0} L
              (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst))))))
      ti ui)
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
  (hujl :
    @LE.le.{0} L
      (@Preorder.toLE.{0} L
        (@PartialOrder.toPreorder.{0} L
          (@SemilatticeInf.toPartialOrder.{0} L
            (@Lattice.toSemilatticeInf.{0} L
              (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst))))))
      uj tl)
  (htkl :
    @LE.le.{0} L
      (@Preorder.toLE.{0} L
        (@PartialOrder.toPreorder.{0} L
          (@SemilatticeInf.toPartialOrder.{0} L
            (@Lattice.toSemilatticeInf.{0} L
              (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst))))))
      tk tl)
  (hukl :
    @LE.le.{0} L
      (@Preorder.toLE.{0} L
        (@PartialOrder.toPreorder.{0} L
          (@SemilatticeInf.toPartialOrder.{0} L
            (@Lattice.toSemilatticeInf.{0} L
              (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst))))))
      uk tl)
  (hgjgi :
    @LE.le.{0} L
      (@Preorder.toLE.{0} L
        (@PartialOrder.toPreorder.{0} L
          (@SemilatticeInf.toPartialOrder.{0} L
            (@Lattice.toSemilatticeInf.{0} L
              (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst))))))
      gj gi)
  (hgkgj :
    @LE.le.{0} L
      (@Preorder.toLE.{0} L
        (@PartialOrder.toPreorder.{0} L
          (@SemilatticeInf.toPartialOrder.{0} L
            (@Lattice.toSemilatticeInf.{0} L
              (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst))))))
      gk gj)
  (hglgk :
    @LE.le.{0} L
      (@Preorder.toLE.{0} L
        (@PartialOrder.toPreorder.{0} L
          (@SemilatticeInf.toPartialOrder.{0} L
            (@Lattice.toSemilatticeInf.{0} L
              (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst))))))
      gl gk)
  (hgil :
    @LE.le.{0} L
      (@Preorder.toLE.{0} L
        (@PartialOrder.toPreorder.{0} L
          (@SemilatticeInf.toPartialOrder.{0} L
            (@Lattice.toSemilatticeInf.{0} L
              (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst))))))
      gi tl)
  (hgli :
    @LE.le.{0} L
      (@Preorder.toLE.{0} L
        (@PartialOrder.toPreorder.{0} L
          (@SemilatticeInf.toPartialOrder.{0} L
            (@Lattice.toSemilatticeInf.{0} L
              (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst))))))
      gl ti)
  (degree b0 b1 a dt dg R : Nat) (hb0 : @Sensitivity213981Formal.ThreeBoundProfiles.BBound L I inst_1 F ti tl b0)
  (hb1 : @Sensitivity213981Formal.ThreeBoundProfiles.BBound L I inst_1 F ui tl b1)
  (ha : @Sensitivity213981Formal.ThreeBoundProfiles.ABound L I inst_1 F gl gi a)
  (hdt : @Sensitivity213981Formal.ThreeBoundProfiles.DBound L I inst_1 F ti tj tk tl dt)
  (hdg : @Sensitivity213981Formal.ThreeBoundProfiles.DBound L I inst_1 F gl gk gj gi dg)
  (x : Prod.{0, 0} (Prod.{0, 0} V Bool) I → Bool) (v : V)
  (hd : @Eq.{1} Nat (@Finset.card.{0} V (@Sensitivity213981Formal.ThreeBoundPositive.outgoing L I V inst_2 S v)) degree)
  (hjmm :
    @Eq.{1} Bool
      (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.mm L I F tj uj
        (@Sensitivity213981Formal.ThreeBoundWitness.child I V x v Bool.false)
        (@Sensitivity213981Formal.ThreeBoundWitness.child I V x v Bool.true))
      Bool.true)
  (hjguard :
    @Eq.{1} Nat
      (@Finset.card.{0} V (@Sensitivity213981Formal.ThreeBoundConditional.guardFailures L I V inst_2 S F gj x v))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (hk :
    ∀ (c : Bool),
      Not
        (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.orientedRow L I V inst_2 S F tk uk gk
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) x v c))
  (haccept :
    ∀ (c : Bool) (y : Prod.{0, 0} (Prod.{0, 0} V Bool) I → Bool),
      @Sensitivity213981Formal.ThreeBoundMinmaxTransfer.orientedRow L I V inst_2 S F ti ui gi
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) y v c →
        @Eq.{1} Bool (G y) Bool.true)
  (hR :
    ∀ (c : Bool),
      @Sensitivity213981Formal.ThreeBoundMinmaxTransfer.orientedRow L I V inst_2 S F tj uj gj
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) x v c →
        @LE.le.{0} Nat instLENat
          (@Finset.card.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I)
            (@Sensitivity213981Formal.ThreeBoundProfiles.flipsTo (Prod.{0, 0} (Prod.{0, 0} V Bool) I)
              (@instFintypeProd.{0, 0} (Prod.{0, 0} V Bool) I (@instFintypeProd.{0, 0} V Bool inst_2 Bool.fintype)
                inst_1)
              (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.orientedRowBool L I V inst_2 S F ti ui gi
                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) v c)
              Bool.false x))
          R),
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
          (@instFintypeProd.{0, 0} (Prod.{0, 0} V Bool) I (@instFintypeProd.{0, 0} V Bool inst_2 Bool.fintype) inst_1) G
          Bool.false x)
        (@Sensitivity213981Formal.ThreeBoundProfiles.flipsTo (Prod.{0, 0} (Prod.{0, 0} V Bool) I)
          (@instFintypeProd.{0, 0} (Prod.{0, 0} V Bool) I (@instFintypeProd.{0, 0} V Bool inst_2 Bool.fintype) inst_1)
          (@Sensitivity213981Formal.ThreeBoundConditional.ordinaryParent L I V inst_2 S F tl gl
            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          Bool.true x)))
    (@Max.max.{0} Nat Nat.instMax R
      (@Max.max.{0} Nat Nat.instMax
        (@ite.{1} Nat
          (@LT.lt.{0} L
            (@Preorder.toLT.{0} L
              (@PartialOrder.toPreorder.{0} L
                (@SemilatticeInf.toPartialOrder.{0} L
                  (@Lattice.toSemilatticeInf.{0} L
                    (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst))))))
            tj tk)
          (@LinearOrder.toDecidableLT.{0} L inst tj tk)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) b1
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) degree a))
            dt)
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@ite.{1} Nat
          (@LT.lt.{0} L
            (@Preorder.toLT.{0} L
              (@PartialOrder.toPreorder.{0} L
                (@SemilatticeInf.toPartialOrder.{0} L
                  (@Lattice.toSemilatticeInf.{0} L
                    (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst))))))
            gk gj)
          (@LinearOrder.toDecidableLT.{0} L inst gk gj)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) b0 b1)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) degree
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                a))
            dg)
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))) := by sorry
