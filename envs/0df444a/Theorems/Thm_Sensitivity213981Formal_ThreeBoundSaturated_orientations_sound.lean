-- Prove2me | Theorems.Thm_Sensitivity213981Formal_ThreeBoundSaturated_orientations_sound
-- name    : Sensitivity213981Formal.ThreeBoundSaturated.orientations_sound
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-26T19:45:21.866852+00:00
-- url     : https://prove2.me/theorems/8060de87-8af2-4666-8833-e1419802a988
-- title:
--   orientations sound — Boolean sensitivity certificate
-- statement:
--   The following universally quantified assertion holds for the finite sets, Boolean families, tournament data, and profile coordinates defined in the imported interfaces. Each binder specifies the domain of its variable, and bracketed conditions specify finite or ordered structures.
--
--   $$
--   \forall V:\mathcal U,\quad \forall \mathit{es}:\operatorname{List}(V\times V),\quad \forall \mathit{ds}:\operatorname{List}(\mathbb B),\quad \forall b:\left(V\to \mathbb N\right),\quad \bigl(\mathit{ds}\in \operatorname{Q2.orientations}\bigl(b, \mathit{es}\bigr)\Longrightarrow \bigl(\bigl(|\mathit{ds}| = |\mathit{es}|\bigr) \land \forall v:V,\quad \bigl(\operatorname{Q2.outCount}\bigl(\mathit{es}, \mathit{ds}, v\bigr) \le b\bigl(v\bigr)\bigr)\bigr)\bigr)
--   $$
--
--   Here $\mathbb B=\{\mathsf{false},\mathsf{true}\}$; $\mathcal P_{\mathrm{fin}}(X)$ denotes the finite subsets of $X$. Named functions and predicates refer to their definitions in the cited source. This result supplies the corresponding orientations sound step in the verified $22$-level sensitivity construction.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; SaturatedOrientations.lean, lines 13–52.

import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_Q2EnumerationBridge
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

theorem Sensitivity213981Formal.ThreeBoundSaturated.orientations_sound :
∀ {V : Type} [inst : DecidableEq.{1} V] (es : List.{0} (Prod.{0, 0} V V)) (ds : List.{0} Bool) (b : V → Nat)
  (h :
    @Membership.mem.{0, 0} (List.{0} Bool) (List.{0} (List.{0} Bool)) (@List.instMembership.{0} (List.{0} Bool))
      (@Sensitivity213981Formal.ThreeBoundQ2.orientations V inst b es) ds),
  And (@Eq.{1} Nat (@List.length.{0} Bool ds) (@List.length.{0} (Prod.{0, 0} V V) es))
    (∀ (v : V), @LE.le.{0} Nat instLENat (@Sensitivity213981Formal.ThreeBoundQ2.outCount V inst es ds v) (b v)) := by sorry
