-- Prove2me | Theorems.Thm_Sensitivity213981Formal_ThreeBoundEndpoint22Regular_allowed_nine_unique
-- name    : Sensitivity213981Formal.ThreeBoundEndpoint22Regular.allowed_nine_unique
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T00:54:56.161585+00:00
-- url     : https://prove2.me/theorems/56c4d820-9631-4199-a092-a771ae01c809
-- title:
--   allowed nine unique — Boolean sensitivity certificate
-- statement:
--   The following universally quantified assertion holds for the finite sets, Boolean families, tournament data, and profile coordinates defined in the imported interfaces. Each binder specifies the domain of its variable, and bracketed conditions specify finite or ordered structures.
--
--   $$
--   \forall \mathit{ts}:\operatorname{List}(\operatorname{Q3.Kind}),\quad \bigl(\bigl(|\mathit{ts}| = 9\bigr)\Longrightarrow \bigl(\operatorname{Q3.allowedTypes}\bigl(\mathit{ts}\bigr)\Longrightarrow \bigl(\mathit{ts} = \operatorname{Endpoint22Regular.allG3}\bigr)\bigr)\bigr)
--   $$
--
--   Here $\mathbb B=\{\mathsf{false},\mathsf{true}\}$; $\mathcal P_{\mathrm{fin}}(X)$ denotes the finite subsets of $X$. Named functions and predicates refer to their definitions in the cited source. This result supplies the corresponding allowed nine unique step in the verified $22$-level sensitivity construction.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22RegularRecord.lean, lines 62–95.

import Definitions.Def_Sensitivity213981Formal_Endpoint22RegularRecord
import Definitions.Def_Sensitivity213981Formal_HighTypeCore
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
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
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Sort
import Mathlib.Data.Prod.Lex
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem Sensitivity213981Formal.ThreeBoundEndpoint22Regular.allowed_nine_unique :
∀ (ts : List.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind)
  (hlen :
    @Eq.{1} Nat (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts)
      (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9))))
  (ht : Sensitivity213981Formal.ThreeBoundQ3.allowedTypes ts),
  @Eq.{1} (List.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind) ts
    Sensitivity213981Formal.ThreeBoundEndpoint22Regular.allG3 := by sorry
