-- Prove2me | Theorems.Thm_Sensitivity213981Formal_ThreeBoundRelaxedPacked_Tree_matches_rows
-- name    : Sensitivity213981Formal.ThreeBoundRelaxedPacked.Tree.matches_rows
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T01:52:46.135947+00:00
-- url     : https://prove2.me/theorems/4725426a-0858-4279-8554-9025eb2f476c
-- title:
--   matches rows — Boolean sensitivity certificate
-- statement:
--   The following universally quantified assertion holds for the finite sets, Boolean families, tournament data, and profile coordinates defined in the imported interfaces. Each binder specifies the domain of its variable, and bracketed conditions specify finite or ordered structures.
--
--   $$
--   \forall t:\operatorname{RelaxedPacked.Tree},\quad \forall u:\operatorname{RecordLookup.Tree},\quad \bigl(\operatorname{Tree.Matches}\bigl(t, u\bigr)\Longrightarrow \bigl(\operatorname{Tree.rows}\bigl(t\bigr) = \operatorname{Tree.elements}\bigl(u\bigr)\bigr)\bigr)
--   $$
--
--   Here $\mathbb B=\{\mathsf{false},\mathsf{true}\}$; $\mathcal P_{\mathrm{fin}}(X)$ denotes the finite subsets of $X$. Named functions and predicates refer to their definitions in the cited source. This result supplies the corresponding matches rows step in the verified $22$-level sensitivity construction.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; RelaxedPackedTreeMatch.lean, lines 10–23.

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

theorem Sensitivity213981Formal.ThreeBoundRelaxedPacked.Tree.matches_rows :
∀ (t : Sensitivity213981Formal.ThreeBoundRelaxedPacked.Tree) (u : Sensitivity213981Formal.ThreeBoundRecordLookup.Tree)
  (h : Sensitivity213981Formal.ThreeBoundRelaxedPacked.Tree.Matches t u),
  @Eq.{1} (List.{0} (List.{0} Nat)) (Sensitivity213981Formal.ThreeBoundRelaxedPacked.Tree.rows t)
    (Sensitivity213981Formal.ThreeBoundRecordLookup.Tree.elements u) := by sorry
