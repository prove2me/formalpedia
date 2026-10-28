-- Prove2me | Theorems.Thm_Sensitivity213981Formal_ThreeBoundRelaxed_mem_options
-- name    : Sensitivity213981Formal.ThreeBoundRelaxed.mem_options
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T01:57:07.401325+00:00
-- url     : https://prove2.me/theorems/62dc9762-785b-4e96-a645-b62f41c5b607
-- title:
--   mem options — Boolean sensitivity certificate
-- statement:
--   The following universally quantified assertion holds for the finite sets, Boolean families, tournament data, and profile coordinates defined in the imported interfaces. Each binder specifies the domain of its variable, and bracketed conditions specify finite or ordered structures.
--
--   $$
--   \forall n:\mathbb N,\quad \forall \mathit{ng}:\mathbb N,\quad \forall s:\operatorname{Relaxed.State},\quad \bigl(\operatorname{Relaxed.Local}\bigl(n, \mathit{ng}, s\bigr)\Longrightarrow s\in \operatorname{Relaxed.options}\bigl(n, \mathit{ng}, \operatorname{State.kind}\bigl(s\bigr)\bigr)\bigr)
--   $$
--
--   Here $\mathbb B=\{\mathsf{false},\mathsf{true}\}$; $\mathcal P_{\mathrm{fin}}(X)$ denotes the finite subsets of $X$. Named functions and predicates refer to their definitions in the cited source. This result supplies the corresponding mem options step in the verified $22$-level sensitivity construction.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; RelaxedStateSearch.lean, lines 35–47.

import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_RelaxedStateSearch
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
import Mathlib.Data.Prod.Lex
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem Sensitivity213981Formal.ThreeBoundRelaxed.mem_options :
∀ (n ng : Nat) (s : Sensitivity213981Formal.ThreeBoundRelaxed.State)
  (hs : Sensitivity213981Formal.ThreeBoundRelaxed.Local n ng s),
  @Membership.mem.{0, 0} Sensitivity213981Formal.ThreeBoundRelaxed.State
    (List.{0} Sensitivity213981Formal.ThreeBoundRelaxed.State)
    (@List.instMembership.{0} Sensitivity213981Formal.ThreeBoundRelaxed.State)
    (Sensitivity213981Formal.ThreeBoundRelaxed.options n ng (Sensitivity213981Formal.ThreeBoundRelaxed.State.kind s)) s := by sorry
