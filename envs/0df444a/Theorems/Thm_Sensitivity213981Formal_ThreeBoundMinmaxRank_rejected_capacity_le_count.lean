-- Prove2me | Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxRank_rejected_capacity_le_count
-- name    : Sensitivity213981Formal.ThreeBoundMinmaxRank.rejected_capacity_le_count
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T01:32:15.864677+00:00
-- url     : https://prove2.me/theorems/8fb7b7a6-f02e-42ce-856a-11ba0cba0eed
-- title:
--   rejected capacity le count — Boolean sensitivity certificate
-- statement:
--   The following universally quantified assertion holds for the finite sets, Boolean families, tournament data, and profile coordinates defined in the imported interfaces. Each binder specifies the domain of its variable, and bracketed conditions specify finite or ordered structures.
--
--   $$
--   \forall n:\mathbb N,\quad \forall I:\mathcal U,\quad \forall V:\mathcal U,\quad \bigl[\mathrm{finite}(I)\bigr]\;\bigl[\mathrm{finite}(V)\bigr]\;\forall S:\operatorname{Witness.Stage}\bigl(\{0,\ldots,n-1\}, I, V\bigr),\quad \forall F:\left(\{0,\ldots,n-1\}\to \left(\left(I\to \mathbb B\right)\to \mathbb B\right)\right),\quad \bigl(\operatorname{Profiles.Nested}\bigl(F\bigr)\Longrightarrow \forall j:\{0,\ldots,n-1\},\quad \forall k:\{0,\ldots,n-1\},\quad \forall P:\operatorname{MinmaxTransfer.PairData}\bigl(S, F, j, k\bigr),\quad \forall a:\operatorname{MinmaxRank.Entry},\quad \forall c:\operatorname{MinmaxRank.Entry},\quad \bigl(\operatorname{MinmaxNumeric.EntryMatch}\bigl(S, F, j, k, P, a, c\bigr)\Longrightarrow \forall x:\left(V\times \mathbb B\times I\to \mathbb B\right),\quad \forall w:V,\quad \forall \mathit{side}:\mathbb B,\quad \forall \mathit{rx}:\{0,\ldots,n-1\},\quad \forall \mathit{ry}:\{0,\ldots,n-1\},\quad \bigl(\operatorname{RankProfiles.RankState}\bigl(F, \operatorname{Witness.child}\bigl(x, w, \operatorname{Bool.not}\bigl(\mathit{side}\bigr)\bigr), \mathit{rx}\bigr)\Longrightarrow \bigl(\operatorname{RankProfiles.RankState}\bigl(F, \operatorname{Witness.child}\bigl(x, w, \mathit{side}\bigr), \mathit{ry}\bigr)\Longrightarrow \bigl(\bigl(\mathit{rx} \le \mathit{ry}\bigr)\Longrightarrow \bigl(\bigl(\operatorname{Witness.parent}\bigl(S, F, k, x\bigr) = \mathsf{false}\bigr)\Longrightarrow \bigl(\operatorname{MinmaxRank.capacityHeight}\bigl(c, \mathit{rx}, \mathit{ry}\bigr) \le |\operatorname{Witness.failed}\bigl(S, F, k, x, w\bigr)|\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)
--   $$
--
--   Here $\mathbb B=\{\mathsf{false},\mathsf{true}\}$; $\mathcal P_{\mathrm{fin}}(X)$ denotes the finite subsets of $X$. Named functions and predicates refer to their definitions in the cited source. This result supplies the corresponding rejected capacity le count step in the verified $22$-level sensitivity construction.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; MinmaxRankData.lean, lines 87–103.

import Definitions.Def_Sensitivity213981Formal_MinmaxEntryMatch
import Definitions.Def_Sensitivity213981Formal_MinmaxPairData
import Definitions.Def_Sensitivity213981Formal_MinmaxRankData
import Definitions.Def_Sensitivity213981Formal_MinmaxRankExpressions
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

theorem Sensitivity213981Formal.ThreeBoundMinmaxRank.rejected_capacity_le_count :
∀ {n : Nat} {I V : Type} [Fintype.{0} I] [inst : Fintype.{0} V]
  (S : Sensitivity213981Formal.ThreeBoundWitness.Stage (Fin n) I V) (F : Fin n → (I → Bool) → Bool)
  (hF :
    @Sensitivity213981Formal.ThreeBoundProfiles.Nested (Fin n) I
      (@PartialOrder.toPreorder.{0} (Fin n) (@Fin.instPartialOrder n)) F)
  (j k : Fin n)
  (P :
    @Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData (Fin n) I V
      (@PartialOrder.toPreorder.{0} (Fin n) (@Fin.instPartialOrder n)) S F j k)
  (a c : Sensitivity213981Formal.ThreeBoundMinmaxRank.Entry)
  (hm : @Sensitivity213981Formal.ThreeBoundMinmaxNumeric.EntryMatch n I V S F j k P a c)
  (x : Prod.{0, 0} (Prod.{0, 0} V Bool) I → Bool) (w : V) (side : Bool) (rx ry : Fin n)
  (hx :
    @Sensitivity213981Formal.ThreeBoundRankProfiles.RankState n I F
      (@Sensitivity213981Formal.ThreeBoundWitness.child I V x w (Bool.not side)) rx)
  (hy :
    @Sensitivity213981Formal.ThreeBoundRankProfiles.RankState n I F
      (@Sensitivity213981Formal.ThreeBoundWitness.child I V x w side) ry)
  (hxy : @LE.le.{0} (Fin n) (@instLEFin n) rx ry)
  (hoff : @Eq.{1} Bool (@Sensitivity213981Formal.ThreeBoundWitness.parent (Fin n) I V inst S F k x) Bool.false),
  @LE.le.{0} Nat instLENat
    (Sensitivity213981Formal.ThreeBoundMinmaxRank.capacityHeight c (@Fin.val n rx) (@Fin.val n ry))
    (@Finset.card.{0} V (@Sensitivity213981Formal.ThreeBoundWitness.failed (Fin n) I V inst S F k x w)) := by sorry
