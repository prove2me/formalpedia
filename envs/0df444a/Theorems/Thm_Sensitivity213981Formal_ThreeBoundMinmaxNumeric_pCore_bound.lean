-- Prove2me | Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_pCore_bound
-- name    : Sensitivity213981Formal.ThreeBoundMinmaxNumeric.pCore_bound
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T01:31:50.954765+00:00
-- url     : https://prove2.me/theorems/ca563997-0016-4def-9096-ee69346dca63
-- title:
--   p Core bound — Boolean sensitivity certificate
-- statement:
--   The following universally quantified assertion holds for the finite sets, Boolean families, tournament data, and profile coordinates defined in the imported interfaces. Each binder specifies the domain of its variable, and bracketed conditions specify finite or ordered structures.
--
--   $$
--   \forall n:\mathbb N,\quad \forall I:\mathcal U,\quad \forall V:\mathcal U,\quad \bigl[\mathrm{finite}(I)\bigr]\;\bigl[\mathrm{finite}(V)\bigr]\;\forall S:\operatorname{Witness.Stage}\bigl(\{0,\ldots,n-1\}, I, V\bigr),\quad \bigl(\operatorname{TournamentHighRows.IsTournament}\bigl(\operatorname{Stage.Adj}\bigl(S\bigr)\bigr)\Longrightarrow \forall F:\left(\{0,\ldots,n-1\}\to \left(\left(I\to \mathbb B\right)\to \mathbb B\right)\right),\quad \bigl(\operatorname{Profiles.Nested}\bigl(F\bigr)\Longrightarrow \forall \mathit{recipe}:\left(\{0,\ldots,n-1\}\to \operatorname{MinmaxNumeric.Entry}\right),\quad \forall j:\{0,\ldots,n-1\},\quad \forall k:\{0,\ldots,n-1\},\quad \forall l:\{0,\ldots,n-1\},\quad \forall P:\operatorname{MinmaxTransfer.PairData}\bigl(S, F, j, k\bigr),\quad \forall Q:\operatorname{MinmaxTransfer.PairData}\bigl(S, F, k, l\bigr),\quad \bigl(\operatorname{MinmaxNumeric.EntryMatch}\bigl(S, F, j, k, P, \mathit{recipe}\bigl(j\bigr), \mathit{recipe}\bigl(k\bigr)\bigr)\Longrightarrow \bigl(\operatorname{MinmaxNumeric.EntryMatch}\bigl(S, F, k, l, Q, \mathit{recipe}\bigl(k\bigr), \mathit{recipe}\bigl(l\bigr)\bigr)\Longrightarrow \forall \mathit{pcross}:\mathbb N,\quad \forall \mathit{first}:\mathbb N,\quad \bigl(\operatorname{ResidualCaps.DominatorCardBound}\bigl(\operatorname{Stage.Adj}\bigl(S\bigr), \operatorname{Stage.label}\bigl(S\bigr), 1, \bigl(\mathit{pcross}+1\bigr)\bigr)\Longrightarrow \forall v:\operatorname{FullProfile.Profile}\bigl(n\bigr),\quad \bigl(\operatorname{FullProfile.Upper}\bigl(F, v\bigr)\Longrightarrow \bigl(\operatorname{Profiles.ABound}\bigl(\operatorname{Witness.parent}\bigl(S, F\bigr), k, l, \mathit{first}\bigr)\Longrightarrow \operatorname{Profiles.PBound}\bigl(\operatorname{Witness.parent}\bigl(S, F\bigr), j, k, l, \operatorname{MinmaxNumeric.pCore}\bigl(n, \mathit{pcross}, v, \mathit{recipe}\bigl(j\bigr), \mathit{recipe}\bigl(k\bigr), \mathit{recipe}\bigl(l\bigr), \mathit{first}\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)
--   $$
--
--   Here $\mathbb B=\{\mathsf{false},\mathsf{true}\}$; $\mathcal P_{\mathrm{fin}}(X)$ denotes the finite subsets of $X$. Named functions and predicates refer to their definitions in the cited source. This result supplies the corresponding p Core bound step in the verified $22$-level sensitivity construction.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; MinmaxScalarConditional.lean, lines 34–104.

import Definitions.Def_Sensitivity213981Formal_ClosureHomogeneity
import Definitions.Def_Sensitivity213981Formal_HeadCostExpressions
import Definitions.Def_Sensitivity213981Formal_MinmaxCoreBounds
import Definitions.Def_Sensitivity213981Formal_MinmaxEntryMatch
import Definitions.Def_Sensitivity213981Formal_MinmaxPairM
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_Q2RawExpressions
import Definitions.Def_Sensitivity213981Formal_StrictUnion
import Definitions.Def_Sensitivity213981Formal_Supplement_NumericExpressions
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

theorem Sensitivity213981Formal.ThreeBoundMinmaxNumeric.pCore_bound :
∀ {n : Nat} {I V : Type} [inst : Fintype.{0} I] [inst_1 : Fintype.{0} V]
  (S : Sensitivity213981Formal.ThreeBoundWitness.Stage (Fin n) I V)
  (hT :
    @Sensitivity213981Formal.TournamentHighRows.IsTournament V
      (@Sensitivity213981Formal.ThreeBoundWitness.Stage.Adj (Fin n) I V S))
  (F : Fin n → (I → Bool) → Bool)
  (hF :
    @Sensitivity213981Formal.ThreeBoundProfiles.Nested (Fin n) I
      (@PartialOrder.toPreorder.{0} (Fin n) (@Fin.instPartialOrder n)) F)
  (recipe : Fin n → Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Entry) (j k l : Fin n)
  (P :
    @Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData (Fin n) I V
      (@PartialOrder.toPreorder.{0} (Fin n) (@Fin.instPartialOrder n)) S F j k)
  (Q :
    @Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData (Fin n) I V
      (@PartialOrder.toPreorder.{0} (Fin n) (@Fin.instPartialOrder n)) S F k l)
  (hm : @Sensitivity213981Formal.ThreeBoundMinmaxNumeric.EntryMatch n I V S F j k P (recipe j) (recipe k))
  (hn : @Sensitivity213981Formal.ThreeBoundMinmaxNumeric.EntryMatch n I V S F k l Q (recipe k) (recipe l))
  (pcross first : Nat)
  (hcap :
    @Sensitivity213981Formal.ResidualCaps.DominatorCardBound V
      (fun (a b : V) => Classical.propDecidable (@Eq.{1} V a b))
      (@Sensitivity213981Formal.ThreeBoundWitness.Stage.Adj (Fin n) I V S)
      (@Sensitivity213981Formal.ThreeBoundWitness.Stage.label (Fin n) I V S)
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) pcross
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (v : Sensitivity213981Formal.ThreeBoundFullProfile.Profile n)
  (hv : @Sensitivity213981Formal.ThreeBoundFullProfile.Upper n I inst F v)
  (hA :
    @Sensitivity213981Formal.ThreeBoundProfiles.ABound (Fin n) (Prod.{0, 0} (Prod.{0, 0} V Bool) I)
      (@instFintypeProd.{0, 0} (Prod.{0, 0} V Bool) I (@instFintypeProd.{0, 0} V Bool inst_1 Bool.fintype) inst)
      (@Sensitivity213981Formal.ThreeBoundWitness.parent (Fin n) I V inst_1 S F) k l first),
  @Sensitivity213981Formal.ThreeBoundProfiles.PBound (Fin n) (Prod.{0, 0} (Prod.{0, 0} V Bool) I)
    (@instFintypeProd.{0, 0} (Prod.{0, 0} V Bool) I (@instFintypeProd.{0, 0} V Bool inst_1 Bool.fintype) inst)
    (@Sensitivity213981Formal.ThreeBoundWitness.parent (Fin n) I V inst_1 S F) j k l
    (Sensitivity213981Formal.ThreeBoundMinmaxNumeric.pCore n pcross v (recipe j) (recipe k) (recipe l) first) := by sorry
