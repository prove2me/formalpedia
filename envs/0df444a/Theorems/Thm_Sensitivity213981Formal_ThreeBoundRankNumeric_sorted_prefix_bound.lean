-- Prove2me | Theorems.Thm_Sensitivity213981Formal_ThreeBoundRankNumeric_sorted_prefix_bound
-- name    : Sensitivity213981Formal.ThreeBoundRankNumeric.sorted_prefix_bound
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-26T18:32:56.302563+00:00
-- url     : https://prove2.me/theorems/d3aadeeb-9392-42ce-a8e5-435cd7a1f64d
-- title:
--   sorted prefix bound — Boolean sensitivity certificate
-- statement:
--   The following universally quantified assertion holds for the finite sets, Boolean families, tournament data, and profile coordinates defined in the imported interfaces. Each binder specifies the domain of its variable, and bracketed conditions specify finite or ordered structures.
--
--   $$
--   \forall \mathit{xs}:\operatorname{List}(\mathbb N),\quad \bigl(\operatorname{List.Pairwise}\bigl(\left(\mathit{x1}\mapsto \left(\mathit{x2}\mapsto \bigl(\mathit{x1} \le \mathit{x2}\bigr)\right)\right), \mathit{xs}\bigr)\Longrightarrow \forall m:\mathbb N,\quad \bigl(\bigl(m \le |\mathit{xs}|\bigr)\Longrightarrow \bigl(\operatorname{List.sum}\bigl(\operatorname{List.take}\bigl(m, \mathit{xs}\bigr)\bigr) \le \operatorname{RankNumeric.allowance}\bigl(m, \operatorname{List.sum}\bigl(\mathit{xs}\bigr), |\mathit{xs}|\bigr)\bigr)\bigr)\bigr)
--   $$
--
--   Here $\mathbb B=\{\mathsf{false},\mathsf{true}\}$; $\mathcal P_{\mathrm{fin}}(X)$ denotes the finite subsets of $X$. Named functions and predicates refer to their definitions in the cited source. This result supplies the corresponding sorted prefix bound step in the verified $22$-level sensitivity construction.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; RankSmallAverage.lean, lines 30–48.

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

theorem Sensitivity213981Formal.ThreeBoundRankNumeric.sorted_prefix_bound :
∀ (xs : List.{0} Nat) (hs : @List.Pairwise.{0} Nat (fun (x1 x2 : Nat) => @LE.le.{0} Nat instLENat x1 x2) xs) (m : Nat)
  (hm : @LE.le.{0} Nat instLENat m (@List.length.{0} Nat xs)),
  @LE.le.{0} Nat instLENat
    (@List.sum.{0} Nat instAddNat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) (@List.take.{0} Nat m xs))
    (Sensitivity213981Formal.ThreeBoundRankNumeric.allowance m
      (@List.sum.{0} Nat instAddNat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) xs) (@List.length.{0} Nat xs)) := by sorry
