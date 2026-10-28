-- Prove2me | Theorems.Thm_Sensitivity213981Formal_ThreeBoundRankNumeric_local_rank_cost
-- name    : Sensitivity213981Formal.ThreeBoundRankNumeric.local_rank_cost
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-26T20:08:58.959983+00:00
-- url     : https://prove2.me/theorems/24fff1b2-9aa0-427d-b1f1-67a04ef3a8d2
-- title:
--   local rank cost — Boolean sensitivity certificate
-- statement:
--   The following universally quantified assertion holds for the finite sets, Boolean families, tournament data, and profile coordinates defined in the imported interfaces. Each binder specifies the domain of its variable, and bracketed conditions specify finite or ordered structures.
--
--   $$
--   \forall n:\mathbb N,\quad \forall I:\mathcal U,\quad \bigl[\mathrm{finite}(I)\bigr]\;\forall F:\left(\{0,\ldots,n-1\}\to \left(\left(I\to \mathbb B\right)\to \mathbb B\right)\right),\quad \bigl(\operatorname{Profiles.Nested}\bigl(F\bigr)\Longrightarrow \forall v:\operatorname{FullProfile.Profile}\bigl(n\bigr),\quad \bigl(\operatorname{FullProfile.Upper}\bigl(F, v\bigr)\Longrightarrow \forall x:\left(I\to \mathbb B\right),\quad \forall y:\left(I\to \mathbb B\right),\quad \forall \mathit{rx}:\{0,\ldots,n-1\},\quad \forall \mathit{ry}:\{0,\ldots,n-1\},\quad \forall g:\{0,\ldots,n-1\},\quad \forall t:\{0,\ldots,n-1\},\quad \forall u:\{0,\ldots,n-1\},\quad \bigl(\operatorname{RankProfiles.RankState}\bigl(F, x, \mathit{rx}\bigr)\Longrightarrow \bigl(\operatorname{RankProfiles.RankState}\bigl(F, y, \mathit{ry}\bigr)\Longrightarrow \bigl(\bigl(g \le \mathit{rx}\bigr)\Longrightarrow \bigl(\bigl(t \le u\bigr)\Longrightarrow \bigl(\bigl(\operatorname{MinmaxTransfer.mm}\bigl(F, t, u, x, y\bigr) = \mathsf{false}\bigr)\Longrightarrow \forall e:\operatorname{RankNumeric.Entry},\quad \forall b:\mathbb N,\quad \bigl(\bigl(g = \operatorname{Entry.guard}\bigl(e\bigr)\bigr)\Longrightarrow \bigl(\bigl(t = \operatorname{Entry.lowerAt}\bigl(e, b\bigr)\bigr)\Longrightarrow \bigl(\bigl(u = \operatorname{Entry.upperAt}\bigl(e, b\bigr)\bigr)\Longrightarrow \bigl(\bigl(|\operatorname{Profiles.flipsTo}\bigl(\left(z\mapsto \operatorname{MinmaxTransfer.mm}\bigl(F, t, u, z, y\bigr)\right), \mathsf{true}, x\bigr)| \le \operatorname{Expr.eval}\bigl(v, \operatorname{RankNumeric.rankUp}\bigl(n, e, \operatorname{Option.some}\bigl(b\bigr), \mathit{rx}, \mathit{ry}\bigr)\bigr)\bigr) \land \bigl(|\operatorname{Union.union}\bigl(\operatorname{Profiles.flipsTo}\bigl(\left(z\mapsto \operatorname{MinmaxTransfer.mm}\bigl(F, t, u, z, y\bigr)\right), \mathsf{true}, x\bigr), \operatorname{Profiles.flipsTo}\bigl(F\bigl(g\bigr), \mathsf{false}, x\bigr)\bigr)| \le \operatorname{Expr.eval}\bigl(v, \operatorname{RankNumeric.rankJoint}\bigl(n, e, \operatorname{Option.some}\bigl(b\bigr), \mathit{rx}, \mathit{ry}\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)
--   $$
--
--   Here $\mathbb B=\{\mathsf{false},\mathsf{true}\}$; $\mathcal P_{\mathrm{fin}}(X)$ denotes the finite subsets of $X$. Named functions and predicates refer to their definitions in the cited source. This result supplies the corresponding local rank cost step in the verified $22$-level sensitivity construction.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; RankLocal.lean, lines 26–92.

import Definitions.Def_Sensitivity213981Formal_MinmaxB
import Definitions.Def_Sensitivity213981Formal_MinmaxHeadLocal
import Definitions.Def_Sensitivity213981Formal_MinmaxPairData
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_Q2RawExpressions
import Definitions.Def_Sensitivity213981Formal_RankExpressions
import Definitions.Def_Sensitivity213981Formal_RankProfileBounds
import Definitions.Def_Sensitivity213981Formal_Supplement_FullProfileClosure
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

theorem Sensitivity213981Formal.ThreeBoundRankNumeric.local_rank_cost :
∀ {n : Nat} {I : Type} [inst : Fintype.{0} I] (F : Fin n → (I → Bool) → Bool)
  (hF :
    @Sensitivity213981Formal.ThreeBoundProfiles.Nested (Fin n) I
      (@PartialOrder.toPreorder.{0} (Fin n) (@Fin.instPartialOrder n)) F)
  (v : Sensitivity213981Formal.ThreeBoundFullProfile.Profile n)
  (hv : @Sensitivity213981Formal.ThreeBoundFullProfile.Upper n I inst F v) (x y : I → Bool) (rx ry g t u : Fin n)
  (hx : @Sensitivity213981Formal.ThreeBoundRankProfiles.RankState n I F x rx)
  (hy : @Sensitivity213981Formal.ThreeBoundRankProfiles.RankState n I F y ry)
  (hg : @LE.le.{0} (Fin n) (@instLEFin n) g rx) (htu : @LE.le.{0} (Fin n) (@instLEFin n) t u)
  (hoff : @Eq.{1} Bool (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.mm (Fin n) I F t u x y) Bool.false)
  (e : Sensitivity213981Formal.ThreeBoundRankNumeric.Entry) (b : Nat)
  (heG : @Eq.{1} Nat (@Fin.val n g) (Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Entry.guard e))
  (heT : @Eq.{1} Nat (@Fin.val n t) (Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Entry.lowerAt e b))
  (heU : @Eq.{1} Nat (@Fin.val n u) (Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Entry.upperAt e b)),
  And
    (@LE.le.{0} Nat instLENat
      (@Finset.card.{0} I
        (@Sensitivity213981Formal.ThreeBoundProfiles.flipsTo I inst
          (fun (z : I → Bool) => @Sensitivity213981Formal.ThreeBoundMinmaxTransfer.mm (Fin n) I F t u z y) Bool.true x))
      (@Sensitivity213981Formal.ThreeBoundNumeric.Expr.eval n v
        (Sensitivity213981Formal.ThreeBoundRankNumeric.rankUp n e (@Option.some.{0} Nat b) (@Fin.val n rx)
          (@Fin.val n ry))))
    (@LE.le.{0} Nat instLENat
      (@Finset.card.{0} I
        (@Union.union.{0} (Finset.{0} I)
          (@Finset.instUnion.{0} I fun (a b : I) => Classical.propDecidable (@Eq.{1} I a b))
          (@Sensitivity213981Formal.ThreeBoundProfiles.flipsTo I inst
            (fun (z : I → Bool) => @Sensitivity213981Formal.ThreeBoundMinmaxTransfer.mm (Fin n) I F t u z y) Bool.true
            x)
          (@Sensitivity213981Formal.ThreeBoundProfiles.flipsTo I inst (F g) Bool.false x)))
      (@Sensitivity213981Formal.ThreeBoundNumeric.Expr.eval n v
        (Sensitivity213981Formal.ThreeBoundRankNumeric.rankJoint n e (@Option.some.{0} Nat b) (@Fin.val n rx)
          (@Fin.val n ry)))) := by sorry
