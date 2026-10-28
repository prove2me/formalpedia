-- Prove2me | Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxRank_target_rank_bound
-- name    : Sensitivity213981Formal.ThreeBoundMinmaxRank.target_rank_bound
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T01:31:58.754085+00:00
-- url     : https://prove2.me/theorems/6b69c1aa-6f32-4e30-9198-ec5a3b7336c1
-- title:
--   target rank bound — Boolean sensitivity certificate
-- statement:
--   The following universally quantified assertion holds for the finite sets, Boolean families, tournament data, and profile coordinates defined in the imported interfaces. Each binder specifies the domain of its variable, and bracketed conditions specify finite or ordered structures.
--
--   $$
--   \forall n:\mathbb N,\quad \forall I:\mathcal U,\quad \forall V:\mathcal U,\quad \bigl[\mathrm{finite}(I)\bigr]\;\bigl[\mathrm{finite}(V)\bigr]\;\forall F:\left(\{0,\ldots,n-1\}\to \left(\left(I\to \mathbb B\right)\to \mathbb B\right)\right),\quad \bigl(\operatorname{Profiles.Nested}\bigl(F\bigr)\Longrightarrow \forall v:\operatorname{FullProfile.Profile}\bigl(n\bigr),\quad \bigl(\operatorname{FullProfile.Upper}\bigl(F, v\bigr)\Longrightarrow \forall e:\operatorname{MinmaxRank.Entry},\quad \forall d:\mathbb N,\quad \forall t:\{0,\ldots,n-1\},\quad \forall u:\{0,\ldots,n-1\},\quad \bigl(\bigl(t \le u\bigr)\Longrightarrow \bigl(\bigl(t = \operatorname{Entry.lowerAt}\bigl(e, d\bigr)\bigr)\Longrightarrow \bigl(\bigl(u = \operatorname{Entry.upperAt}\bigl(e, d\bigr)\bigr)\Longrightarrow \forall x:\left(V\times \mathbb B\times I\to \mathbb B\right),\quad \forall w:V,\quad \forall \mathit{side}:\mathbb B,\quad \forall \mathit{rx}:\{0,\ldots,n-1\},\quad \forall \mathit{ry}:\{0,\ldots,n-1\},\quad \bigl(\operatorname{RankProfiles.RankState}\bigl(F, \operatorname{Witness.child}\bigl(x, w, \operatorname{Bool.not}\bigl(\mathit{side}\bigr)\bigr), \mathit{rx}\bigr)\Longrightarrow \bigl(\operatorname{RankProfiles.RankState}\bigl(F, \operatorname{Witness.child}\bigl(x, w, \mathit{side}\bigr), \mathit{ry}\bigr)\Longrightarrow \bigl(\bigl(\mathit{rx} \le \mathit{ry}\bigr)\Longrightarrow \bigl(\bigl(\operatorname{MinmaxTransfer.mm}\bigl(F, t, u, \operatorname{Witness.child}\bigl(x, w, \mathsf{false}\bigr), \operatorname{Witness.child}\bigl(x, w, \mathsf{true}\bigr)\bigr) = \mathsf{true}\bigr)\Longrightarrow \bigl(|\operatorname{MinmaxTransfer.mmTargetBits}\bigl(F, t, u, x, w\bigr)| \le \operatorname{Expr.eval}\bigl(v, \bigl(\operatorname{RankProfiles.downRankExpr}\bigl(n, \operatorname{MinmaxRank.need}\bigl(n, e, \mathit{ry}, d\bigr), \mathit{rx}\bigr)+\operatorname{RankProfiles.downRankExpr}\bigl(n, \operatorname{MinmaxRank.need}\bigl(n, e, \mathit{rx}, d\bigr), \mathit{ry}\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)
--   $$
--
--   Here $\mathbb B=\{\mathsf{false},\mathsf{true}\}$; $\mathcal P_{\mathrm{fin}}(X)$ denotes the finite subsets of $X$. Named functions and predicates refer to their definitions in the cited source. This result supplies the corresponding target rank bound step in the verified $22$-level sensitivity construction.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; MinmaxRankLocal.lean, lines 118–144.

import Definitions.Def_Sensitivity213981Formal_MinmaxB
import Definitions.Def_Sensitivity213981Formal_MinmaxEntryMatch
import Definitions.Def_Sensitivity213981Formal_MinmaxPairData
import Definitions.Def_Sensitivity213981Formal_MinmaxRankExpressions
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_Q2RawExpressions
import Definitions.Def_Sensitivity213981Formal_RankProfileBounds
import Definitions.Def_Sensitivity213981Formal_Supplement_FullProfileClosure
import Definitions.Def_Sensitivity213981Formal_Supplement_GradedPositiveBoundary
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

theorem Sensitivity213981Formal.ThreeBoundMinmaxRank.target_rank_bound :
∀ {n : Nat} {I V : Type} [inst : Fintype.{0} I] [Fintype.{0} V] (F : Fin n → (I → Bool) → Bool)
  (hF :
    @Sensitivity213981Formal.ThreeBoundProfiles.Nested (Fin n) I
      (@PartialOrder.toPreorder.{0} (Fin n) (@Fin.instPartialOrder n)) F)
  (v : Sensitivity213981Formal.ThreeBoundFullProfile.Profile n)
  (hv : @Sensitivity213981Formal.ThreeBoundFullProfile.Upper n I inst F v)
  (e : Sensitivity213981Formal.ThreeBoundMinmaxRank.Entry) (d : Nat) (t u : Fin n)
  (htu : @LE.le.{0} (Fin n) (@instLEFin n) t u)
  (ht : @Eq.{1} Nat (@Fin.val n t) (Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Entry.lowerAt e d))
  (hu : @Eq.{1} Nat (@Fin.val n u) (Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Entry.upperAt e d))
  (x : Prod.{0, 0} (Prod.{0, 0} V Bool) I → Bool) (w : V) (side : Bool) (rx ry : Fin n)
  (hx :
    @Sensitivity213981Formal.ThreeBoundRankProfiles.RankState n I F
      (@Sensitivity213981Formal.ThreeBoundWitness.child I V x w (Bool.not side)) rx)
  (hy :
    @Sensitivity213981Formal.ThreeBoundRankProfiles.RankState n I F
      (@Sensitivity213981Formal.ThreeBoundWitness.child I V x w side) ry)
  (hxy : @LE.le.{0} (Fin n) (@instLEFin n) rx ry)
  (hmm :
    @Eq.{1} Bool
      (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.mm (Fin n) I F t u
        (@Sensitivity213981Formal.ThreeBoundWitness.child I V x w Bool.false)
        (@Sensitivity213981Formal.ThreeBoundWitness.child I V x w Bool.true))
      Bool.true),
  @LE.le.{0} Nat instLENat
    (@Finset.card.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I)
      (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.mmTargetBits (Fin n) I V inst F t u x w))
    (@Sensitivity213981Formal.ThreeBoundNumeric.Expr.eval n v
      (@HAdd.hAdd.{0, 0, 0} (Sensitivity213981Formal.ThreeBoundNumeric.Expr n)
        (Sensitivity213981Formal.ThreeBoundNumeric.Expr n) (Sensitivity213981Formal.ThreeBoundNumeric.Expr n)
        (@instHAdd.{0} (Sensitivity213981Formal.ThreeBoundNumeric.Expr n)
          (@Sensitivity213981Formal.ThreeBoundNumeric.instAddExpr_q2RawExpressions n))
        (Sensitivity213981Formal.ThreeBoundRankProfiles.downRankExpr n
          (Sensitivity213981Formal.ThreeBoundMinmaxRank.need n e (@Fin.val n ry) d) (@Fin.val n rx))
        (Sensitivity213981Formal.ThreeBoundRankProfiles.downRankExpr n
          (Sensitivity213981Formal.ThreeBoundMinmaxRank.need n e (@Fin.val n rx) d) (@Fin.val n ry)))) := by sorry
