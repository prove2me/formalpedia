-- Prove2me | Theorems.Thm_Sensitivity213981Formal_ThreeBoundMarkers_exists_markers_of_sorted_prefix
-- name    : Sensitivity213981Formal.ThreeBoundMarkers.exists_markers_of_sorted_prefix
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-26T18:34:23.853166+00:00
-- url     : https://prove2.me/theorems/08bce0bf-c892-4aca-9fc6-725bdf684c57
-- title:
--   exists markers of sorted prefix — Boolean sensitivity certificate
-- statement:
--   The following universally quantified assertion holds for the finite sets, Boolean families, tournament data, and profile coordinates defined in the imported interfaces. Each binder specifies the domain of its variable, and bracketed conditions specify finite or ordered structures.
--
--   $$
--   \forall V:\mathcal U,\quad \forall \mathit{vs}:\operatorname{List}(V),\quad \bigl(\operatorname{List.Nodup}\bigl(\mathit{vs}\bigr)\Longrightarrow \forall \mathit{res}:\left(V\to \mathbb N\right),\quad \forall k:\mathbb N,\quad \bigl(\bigl(k \le |\mathit{vs}|\bigr)\Longrightarrow \exists M:\mathcal P_{\mathrm{fin}}(V),\quad \bigl(\bigl(M \le \operatorname{List.toFinset}\bigl(\mathit{vs}\bigr)\bigr) \land \bigl(\bigl(|M| = k\bigr) \land \bigl(\sum_{v\in M} \mathit{res}\bigl(v\bigr) = \operatorname{List.sum}\bigl(\operatorname{List.take}\bigl(k, \operatorname{List.mergeSort}\bigl(\operatorname{List.map}\bigl(\mathit{res}, \mathit{vs}\bigr), \left(\mathit{x1}\mapsto \left(\mathit{x2}\mapsto \operatorname{decide}(\bigl(\mathit{x1} \le \mathit{x2}\bigr))\right)\right)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)\bigr)
--   $$
--
--   Here $\mathbb B=\{\mathsf{false},\mathsf{true}\}$; $\mathcal P_{\mathrm{fin}}(X)$ denotes the finite subsets of $X$. Named functions and predicates refer to their definitions in the cited source. This result supplies the corresponding exists markers of sorted prefix step in the verified $22$-level sensitivity construction.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; ResidualSelection.lean, lines 15–31.

import Definitions.Def_Sensitivity213981Formal_GlobalAccounting
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
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

theorem Sensitivity213981Formal.ThreeBoundMarkers.exists_markers_of_sorted_prefix :
∀ {V : Type} [inst : DecidableEq.{1} V] (vs : List.{0} V) (hvs : @List.Nodup.{0} V vs) (res : V → Nat) (k : Nat)
  (hk : @LE.le.{0} Nat instLENat k (@List.length.{0} V vs)),
  @Exists.{1} (Finset.{0} V) fun (M : Finset.{0} V) =>
    And
      (@LE.le.{0} (Finset.{0} V)
        (@Preorder.toLE.{0} (Finset.{0} V)
          (@PartialOrder.toPreorder.{0} (Finset.{0} V) (@Finset.instPartialOrder.{0} V)))
        M (@List.toFinset.{0} V inst vs))
      (And (@Eq.{1} Nat (@Finset.card.{0} V M) k)
        (@Eq.{1} Nat (@Finset.sum.{0, 0} V Nat Nat.instAddCommMonoid M fun (v : V) => res v)
          (@List.sum.{0} Nat instAddNat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass)
            (@List.take.{0} Nat k
              (@List.mergeSort.{0} Nat (@List.map.{0, 0} V Nat res vs) fun (x1 x2 : Nat) =>
                @Decidable.decide (@LE.le.{0} Nat instLENat x1 x2) (Nat.decLe x1 x2)))))) := by sorry
