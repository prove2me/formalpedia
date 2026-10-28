-- Prove2me | Theorems.Thm_Sensitivity213981Formal_ThreeBoundEndpoint22Reachable_covered4_400
-- name    : Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.covered4_400
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T02:59:34.532528+00:00
-- url     : https://prove2.me/theorems/7f102e66-5b8a-4e01-b5ba-b7a47a9975cf
-- title:
--   covered4 400 — Boolean sensitivity certificate
-- statement:
--   The following universally quantified assertion holds for the finite sets, Boolean families, tournament data, and profile coordinates defined in the imported interfaces. Each binder specifies the domain of its variable, and bracketed conditions specify finite or ordered structures.
--
--   $$
--   \operatorname{RelaxedReachable.Covers}\bigl(\operatorname{Endpoint22Packed.tree}, \operatorname{List.take}\bigl(40, \operatorname{List.drop}\bigl(400, \operatorname{Endpoint22Types.types4}\bigr)\bigr)\bigr)
--   $$
--
--   Here $\mathbb B=\{\mathsf{false},\mathsf{true}\}$; $\mathcal P_{\mathrm{fin}}(X)$ denotes the finite subsets of $X$. Named functions and predicates refer to their definitions in the cited source. This result supplies the corresponding covered4 400 step in the verified $22$-level sensitivity construction.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachTypes4.lean, lines 447–489.

import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks000
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks001
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks002
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks003
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks004
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks005
import Definitions.Def_Sensitivity213981Formal_Endpoint22TypeData
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_RelaxedReachableSearch
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
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Prod.Lex
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.covered4_400 :
Sensitivity213981Formal.ThreeBoundRelaxedReachable.Covers Sensitivity213981Formal.ThreeBoundEndpoint22Packed.tree
  (@List.take.{0} (List.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind)
    (@OfNat.ofNat.{0} Nat (nat_lit 40) (instOfNatNat (nat_lit 40)))
    (@List.drop.{0} (List.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind)
      (@OfNat.ofNat.{0} Nat (nat_lit 400) (instOfNatNat (nat_lit 400)))
      Sensitivity213981Formal.ThreeBoundEndpoint22Types.types4)) := by sorry
