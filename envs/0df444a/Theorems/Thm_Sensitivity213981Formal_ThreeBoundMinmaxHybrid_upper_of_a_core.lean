-- Prove2me | Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxHybrid_upper_of_a_core
-- name    : Sensitivity213981Formal.ThreeBoundMinmaxHybrid.upper_of_a_core
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T01:31:52.016824+00:00
-- url     : https://prove2.me/theorems/09ee19e5-3185-426b-9420-70d3e95712a3
-- title:
--   upper of a core — Boolean sensitivity certificate
-- statement:
--   The following universally quantified assertion holds for the finite sets, Boolean families, tournament data, and profile coordinates defined in the imported interfaces. Each binder specifies the domain of its variable, and bracketed conditions specify finite or ordered structures.
--
--   $$
--   \forall n:\mathbb N,\quad \forall I:\mathcal U,\quad \forall V:\mathcal U,\quad \bigl[\mathrm{finite}(I)\bigr]\;\bigl[\mathrm{finite}(V)\bigr]\;\forall S:\operatorname{Witness.Stage}\bigl(\{0,\ldots,n-1\}, I, V\bigr),\quad \bigl(\operatorname{TournamentHighRows.IsTournament}\bigl(\operatorname{Stage.Adj}\bigl(S\bigr)\bigr)\Longrightarrow \forall F:\left(\{0,\ldots,n-1\}\to \left(\left(I\to \mathbb B\right)\to \mathbb B\right)\right),\quad \bigl(\operatorname{Profiles.Nested}\bigl(F\bigr)\Longrightarrow \forall \mathit{recipe}:\left(\{0,\ldots,n-1\}\to \operatorname{MinmaxNumeric.Entry}\right),\quad \forall P:\prod_{i:\{0,\ldots,n-1\}} \prod_{j:\{0,\ldots,n-1\}} \left(\bigl(i \le j\bigr)\to \operatorname{MinmaxTransfer.PairData}\bigl(S, F, i, j\bigr)\right),\quad \bigl(\forall i:\{0,\ldots,n-1\},\quad \forall j:\{0,\ldots,n-1\},\quad \bigl(\bigl(i \le j\bigr)\Longrightarrow \operatorname{MinmaxNumeric.EntryMatch}\bigl(S, F, i, j, P\bigl(i, j, \mathit{hij}\bigr), \mathit{recipe}\bigl(i\bigr), \mathit{recipe}\bigl(j\bigr)\bigr)\bigr)\Longrightarrow \forall \mathit{degree}:\mathbb N,\quad \forall \mathit{pcross}:\mathbb N,\quad \bigl(\forall w:V,\quad \bigl(|\operatorname{Positive.outgoing}\bigl(S, w\bigr)| = \mathit{degree}\bigr)\Longrightarrow \bigl(\operatorname{ResidualCaps.DominatorCardBound}\bigl(\operatorname{Stage.Adj}\bigl(S\bigr), \operatorname{Stage.label}\bigl(S\bigr), 1, \bigl(\mathit{pcross}+1\bigr)\bigr)\Longrightarrow \forall v:\operatorname{FullProfile.Profile}\bigl(n\bigr),\quad \forall w:\operatorname{FullProfile.Profile}\bigl(n\bigr),\quad \bigl(\operatorname{FullProfile.Upper}\bigl(F, v\bigr)\Longrightarrow \bigl(\forall i:\{0,\ldots,n-1\},\quad \forall j:\{0,\ldots,n-1\},\quad \bigl(\bigl(i \le j\bigr)\Longrightarrow \operatorname{Profiles.ABound}\bigl(\operatorname{Witness.parent}\bigl(S, F\bigr), i, j, w\bigl(\operatorname{Coord.a}\bigl(i, j\bigr)\bigr)\bigr)\bigr)\Longrightarrow \bigl(\operatorname{MinmaxHybrid.CoreBounds}\bigl(\mathit{degree}, \mathit{pcross}, \mathit{recipe}, v, w\bigr)\Longrightarrow \operatorname{FullProfile.Upper}\bigl(\operatorname{Witness.parent}\bigl(S, F\bigr), w\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)
--   $$
--
--   Here $\mathbb B=\{\mathsf{false},\mathsf{true}\}$; $\mathcal P_{\mathrm{fin}}(X)$ denotes the finite subsets of $X$. Named functions and predicates refer to their definitions in the cited source. This result supplies the corresponding upper of a core step in the verified $22$-level sensitivity construction.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; MinmaxHybridTransfer.lean, lines 71–131.

import Definitions.Def_Sensitivity213981Formal_MinmaxHybridTransfer
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_ProfileClosures
import Definitions.Def_Sensitivity213981Formal_Q2RawExpressions
import Definitions.Def_Sensitivity213981Formal_Supplement_FullProfileClosure
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

theorem Sensitivity213981Formal.ThreeBoundMinmaxHybrid.upper_of_a_core :
∀ {n : Nat} {I V : Type} [inst : Fintype.{0} I] [inst_1 : Fintype.{0} V]
  (S : Sensitivity213981Formal.ThreeBoundWitness.Stage (Fin n) I V)
  (hT :
    @Sensitivity213981Formal.TournamentHighRows.IsTournament V
      (@Sensitivity213981Formal.ThreeBoundWitness.Stage.Adj (Fin n) I V S))
  (F : Fin n → (I → Bool) → Bool)
  (hF :
    @Sensitivity213981Formal.ThreeBoundProfiles.Nested (Fin n) I
      (@PartialOrder.toPreorder.{0} (Fin n) (@Fin.instPartialOrder n)) F)
  (recipe : Fin n → Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Entry)
  (P :
    (i j : Fin n) →
      @LE.le.{0} (Fin n) (@instLEFin n) i j →
        @Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData (Fin n) I V
          (@PartialOrder.toPreorder.{0} (Fin n) (@Fin.instPartialOrder n)) S F i j)
  (hm :
    ∀ (i j : Fin n) (hij : @LE.le.{0} (Fin n) (@instLEFin n) i j),
      @Sensitivity213981Formal.ThreeBoundMinmaxNumeric.EntryMatch n I V S F i j (P i j hij) (recipe i) (recipe j))
  (degree pcross : Nat)
  (hd :
    ∀ (w : V),
      @Eq.{1} Nat (@Finset.card.{0} V (@Sensitivity213981Formal.ThreeBoundPositive.outgoing (Fin n) I V inst_1 S w))
        degree)
  (hcap :
    @Sensitivity213981Formal.ResidualCaps.DominatorCardBound V
      (fun (a b : V) => Classical.propDecidable (@Eq.{1} V a b))
      (@Sensitivity213981Formal.ThreeBoundWitness.Stage.Adj (Fin n) I V S)
      (@Sensitivity213981Formal.ThreeBoundWitness.Stage.label (Fin n) I V S)
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) pcross
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (v w : Sensitivity213981Formal.ThreeBoundFullProfile.Profile n)
  (hv : @Sensitivity213981Formal.ThreeBoundFullProfile.Upper n I inst F v)
  (hA :
    ∀ (i j : Fin n),
      @LE.le.{0} (Fin n) (@instLEFin n) i j →
        @Sensitivity213981Formal.ThreeBoundProfiles.ABound (Fin n) (Prod.{0, 0} (Prod.{0, 0} V Bool) I)
          (@instFintypeProd.{0, 0} (Prod.{0, 0} V Bool) I (@instFintypeProd.{0, 0} V Bool inst_1 Bool.fintype) inst)
          (@Sensitivity213981Formal.ThreeBoundWitness.parent (Fin n) I V inst_1 S F) i j
          (w (@Sensitivity213981Formal.ThreeBoundFullProfile.Coord.a n i j)))
  (hc : @Sensitivity213981Formal.ThreeBoundMinmaxHybrid.CoreBounds n degree pcross recipe v w),
  @Sensitivity213981Formal.ThreeBoundFullProfile.Upper n (Prod.{0, 0} (Prod.{0, 0} V Bool) I)
    (@instFintypeProd.{0, 0} (Prod.{0, 0} V Bool) I (@instFintypeProd.{0, 0} V Bool inst_1 Bool.fintype) inst)
    (@Sensitivity213981Formal.ThreeBoundWitness.parent (Fin n) I V inst_1 S F) w := by sorry
