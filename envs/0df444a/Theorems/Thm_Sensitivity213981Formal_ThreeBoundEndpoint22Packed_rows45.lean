-- Prove2me | Theorems.Thm_Sensitivity213981Formal_ThreeBoundEndpoint22Packed_rows45
-- name    : Sensitivity213981Formal.ThreeBoundEndpoint22Packed.rows45
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T01:55:44.074629+00:00
-- url     : https://prove2.me/theorems/e4ad5681-0932-4fc6-9105-755fef476be8
-- title:
--   rows45 — Boolean sensitivity certificate
-- statement:
--   The packed record-tree data of batch 045 has the exact structural property asserted by `rows45`. The record tree and all keys, row counts, and partition entries are the fixed finite data in the imported batch. The assertion identifies the stated key list, root shape, or row inventory by equality or its defining finite predicate, as specified by the formal statement. This certificate connects the compressed tree representation to the exhaustive coverage checker.
--
--   $$
--   \bigl(\operatorname{Tree.rows}\bigl(\operatorname{Endpoint22Packed.subtree45}\bigr) = \operatorname{Tree.elements}\bigl(\operatorname{Endpoint22Records.subtree45}\bigr)\bigr)
--   $$
--
--   Here $\mathbb B=\{\mathsf{false},\mathsf{true}\}$; $\mathcal P_{\mathrm{fin}}(X)$ denotes the finite subsets of $X$. Named functions and predicates refer to their definitions in the cited source. This result supplies the corresponding rows45 step in the verified $22$-level sensitivity construction.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22PackedKeys045.lean, lines 22–22.

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedTree045
import Definitions.Def_Sensitivity213981Formal_Endpoint22RecordTreeData045
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_RelaxedPackedTreeMatch
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
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Sort
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Prod.Lex
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem Sensitivity213981Formal.ThreeBoundEndpoint22Packed.rows45 :
@Eq.{1} (List.{0} (List.{0} Nat))
  (Sensitivity213981Formal.ThreeBoundRelaxedPacked.Tree.rows
    Sensitivity213981Formal.ThreeBoundEndpoint22Packed.subtree45)
  (Sensitivity213981Formal.ThreeBoundRecordLookup.Tree.elements
    Sensitivity213981Formal.ThreeBoundEndpoint22Records.subtree45) := by sorry
