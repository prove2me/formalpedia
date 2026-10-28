-- Prove2me | Theorems.Thm_Sensitivity213981Formal_ThreeBoundRankNumeric_exists_markers_allowance
-- name    : Sensitivity213981Formal.ThreeBoundRankNumeric.exists_markers_allowance
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-26T18:39:59.163037+00:00
-- url     : https://prove2.me/theorems/c0ee4b78-14cf-436c-8cb8-b69ba25a9a31
-- title:
--   exists markers allowance — Boolean sensitivity certificate
-- statement:
--   The following universally quantified assertion holds for the finite sets, Boolean families, tournament data, and profile coordinates defined in the imported interfaces. Each binder specifies the domain of its variable, and bracketed conditions specify finite or ordered structures.
--
--   $$
--   \forall V:\mathcal U,\quad \forall G:\mathcal P_{\mathrm{fin}}(V),\quad \forall \mathit{weight}:\left(V\to \mathbb N\right),\quad \forall m:\mathbb N,\quad \bigl(\bigl(m \le |G|\bigr)\Longrightarrow \exists M:\mathcal P_{\mathrm{fin}}(V),\quad \bigl(\bigl(M \le G\bigr) \land \bigl(\bigl(|M| = m\bigr) \land \bigl(\sum_{v\in M} \mathit{weight}\bigl(v\bigr) \le \operatorname{RankNumeric.allowance}\bigl(m, \sum_{v\in G} \mathit{weight}\bigl(v\bigr), |G|\bigr)\bigr)\bigr)\bigr)\bigr)
--   $$
--
--   Here $\mathbb B=\{\mathsf{false},\mathsf{true}\}$; $\mathcal P_{\mathrm{fin}}(X)$ denotes the finite subsets of $X$. Named functions and predicates refer to their definitions in the cited source. This result supplies the corresponding exists markers allowance step in the verified $22$-level sensitivity construction.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; RankSmallAverage.lean, lines 56–71.

import Definitions.Def_Sensitivity213981Formal_GlobalAccounting
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_RankSmallAverage
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Sort
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem Sensitivity213981Formal.ThreeBoundRankNumeric.exists_markers_allowance :
∀ {V : Type} [DecidableEq.{1} V] (G : Finset.{0} V) (weight : V → Nat) (m : Nat)
  (hm : @LE.le.{0} Nat instLENat m (@Finset.card.{0} V G)),
  @Exists.{1} (Finset.{0} V) fun (M : Finset.{0} V) =>
    And
      (@LE.le.{0} (Finset.{0} V)
        (@Preorder.toLE.{0} (Finset.{0} V)
          (@PartialOrder.toPreorder.{0} (Finset.{0} V) (@Finset.instPartialOrder.{0} V)))
        M G)
      (And (@Eq.{1} Nat (@Finset.card.{0} V M) m)
        (@LE.le.{0} Nat instLENat (@Finset.sum.{0, 0} V Nat Nat.instAddCommMonoid M fun (v : V) => weight v)
          (Sensitivity213981Formal.ThreeBoundRankNumeric.allowance m
            (@Finset.sum.{0, 0} V Nat Nat.instAddCommMonoid G fun (v : V) => weight v) (@Finset.card.{0} V G)))) := by sorry
