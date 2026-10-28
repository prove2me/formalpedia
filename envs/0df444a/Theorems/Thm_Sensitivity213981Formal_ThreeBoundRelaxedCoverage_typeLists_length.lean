-- Prove2me | Theorems.Thm_Sensitivity213981Formal_ThreeBoundRelaxedCoverage_typeLists_length
-- name    : Sensitivity213981Formal.ThreeBoundRelaxedCoverage.typeLists_length
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T01:53:17.800289+00:00
-- url     : https://prove2.me/theorems/b8e87abc-09e8-41d4-b045-65399a2a69c4
-- title:
--   type Lists length — Boolean sensitivity certificate
-- statement:
--   The following universally quantified assertion holds for the finite sets, Boolean families, tournament data, and profile coordinates defined in the imported interfaces. Each binder specifies the domain of its variable, and bracketed conditions specify finite or ordered structures.
--
--   $$
--   \forall \mathit{lo}:\mathbb N,\quad \forall n:\mathbb N,\quad \forall \mathit{ts}:\operatorname{List}(\operatorname{Q3.Kind}),\quad \bigl(\mathit{ts}\in \operatorname{Q3.typeLists}\bigl(\mathit{lo}, n\bigr)\Longrightarrow \bigl(|\mathit{ts}| = n\bigr)\bigr)
--   $$
--
--   Here $\mathbb B=\{\mathsf{false},\mathsf{true}\}$; $\mathcal P_{\mathrm{fin}}(X)$ denotes the finite subsets of $X$. Named functions and predicates refer to their definitions in the cited source. This result supplies the corresponding type Lists length step in the verified $22$-level sensitivity construction.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; RelaxedRecordCoverage.lean, lines 15–28.

import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_RelaxedRecordCoverage
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Nat
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
import Mathlib.Data.List.Sort
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Prod.Lex
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem Sensitivity213981Formal.ThreeBoundRelaxedCoverage.typeLists_length :
∀ (lo n : Nat) (ts : List.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind)
  (h :
    @Membership.mem.{0, 0} (List.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind)
      (List.{0} (List.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind))
      (@List.instMembership.{0} (List.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind))
      (Sensitivity213981Formal.ThreeBoundQ3.typeLists lo n) ts),
  @Eq.{1} Nat (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts) n := by sorry
