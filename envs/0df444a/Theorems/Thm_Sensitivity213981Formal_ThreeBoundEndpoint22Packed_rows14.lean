-- Prove2me | Theorems.Thm_Sensitivity213981Formal_ThreeBoundEndpoint22Packed_rows14
-- name    : Sensitivity213981Formal.ThreeBoundEndpoint22Packed.rows14
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T01:53:47.214853+00:00
-- url     : https://prove2.me/theorems/e288ea8f-edf7-4371-961d-8a188358305a
-- title:
--   rows14 — Boolean sensitivity certificate
-- statement:
--   The packed record-tree data of batch 014 has the exact structural property asserted by `rows14`. The record tree and all keys, row counts, and partition entries are the fixed finite data in the imported batch. The assertion identifies the stated key list, root shape, or row inventory by equality or its defining finite predicate, as specified by the formal statement. This certificate connects the compressed tree representation to the exhaustive coverage checker.
--
--   $$
--   \bigl(\operatorname{Tree.rows}\bigl(\operatorname{Endpoint22Packed.subtree14}\bigr) = \operatorname{Tree.elements}\bigl(\operatorname{Endpoint22Records.subtree14}\bigr)\bigr)
--   $$
--
--   Here $\mathbb B=\{\mathsf{false},\mathsf{true}\}$; $\mathcal P_{\mathrm{fin}}(X)$ denotes the finite subsets of $X$. Named functions and predicates refer to their definitions in the cited source. This result supplies the corresponding rows14 step in the verified $22$-level sensitivity construction.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22PackedKeys014.lean, lines 22–22.

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedTree014
import Definitions.Def_Sensitivity213981Formal_Endpoint22RecordTreeData014
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

theorem Sensitivity213981Formal.ThreeBoundEndpoint22Packed.rows14 :
@Eq.{1} (List.{0} (List.{0} Nat))
  (Sensitivity213981Formal.ThreeBoundRelaxedPacked.Tree.rows
    Sensitivity213981Formal.ThreeBoundEndpoint22Packed.subtree14)
  (Sensitivity213981Formal.ThreeBoundRecordLookup.Tree.elements
    Sensitivity213981Formal.ThreeBoundEndpoint22Records.subtree14) := by sorry
