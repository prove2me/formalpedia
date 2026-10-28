-- Prove2me | Theorems.Thm_Sensitivity213981Formal_ThreeBoundQ3RecordFields_incoming_orientation_eq_card
-- name    : Sensitivity213981Formal.ThreeBoundQ3RecordFields.incoming_orientation_eq_card
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T01:32:28.049157+00:00
-- url     : https://prove2.me/theorems/287a38fc-82fb-4c59-bab9-d85af85a2c60
-- title:
--   incoming orientation eq card — Boolean sensitivity certificate
-- statement:
--   The following universally quantified assertion holds for the finite sets, Boolean families, tournament data, and profile coordinates defined in the imported interfaces. Each binder specifies the domain of its variable, and bracketed conditions specify finite or ordered structures.
--
--   $$
--   \forall \mathit{ts}:\operatorname{List}(\operatorname{Q3.Kind}),\quad \forall R:\left(\{0,\ldots,|\mathit{ts}|-1\}\to \left(\{0,\ldots,|\mathit{ts}|-1\}\to \mathrm{Prop}\right)\right),\quad \bigl(\operatorname{TournamentHighRows.IsTournament}\bigl(R\bigr)\Longrightarrow \forall w:\{0,\ldots,|\mathit{ts}|-1\},\quad \bigl(\operatorname{Q3RecordFields.incoming}\bigl(\mathit{ts}, \operatorname{Q2.orientationBits}\bigl(R\bigr), w\bigr) = |\operatorname{Finset.filter}\bigl(\left(v\mapsto \bigl(\bigl(\operatorname{Q3.isGuard}\bigl(\operatorname{List.get}\bigl(\mathit{ts}, v\bigr)\bigr) = \mathsf{true}\bigr) \land R\bigl(v, w\bigr)\bigr)\right), \operatorname{univ}_{\{0,\ldots,|\mathit{ts}|-1\}}\bigr)|\bigr)\bigr)
--   $$
--
--   Here $\mathbb B=\{\mathsf{false},\mathsf{true}\}$; $\mathcal P_{\mathrm{fin}}(X)$ denotes the finite subsets of $X$. Named functions and predicates refer to their definitions in the cited source. This result supplies the corresponding incoming orientation eq card step in the verified $22$-level sensitivity construction.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Q3RecordFields.lean, lines 93–121.

import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_Q2EnumerationBridge
import Definitions.Def_Sensitivity213981Formal_Q3RecordFields
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

theorem Sensitivity213981Formal.ThreeBoundQ3RecordFields.incoming_orientation_eq_card :
∀ (ts : List.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind)
  (R :
    Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts) →
      Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts) → Prop)
  [inst :
    @DecidableRel.{1, 1} (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts))
      (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts)) R]
  (hR :
    @Sensitivity213981Formal.TournamentHighRows.IsTournament
      (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts)) R)
  (w : Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts)),
  @Eq.{1} Nat
    (Sensitivity213981Formal.ThreeBoundQ3RecordFields.incoming ts
      (@Sensitivity213981Formal.ThreeBoundQ2.orientationBits
        (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts) R inst)
      w)
    (@Finset.card.{0} (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts))
      (@Finset.filter.{0} (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts))
        (fun (v : Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts)) =>
          And
            (@Eq.{1} Bool
              (Sensitivity213981Formal.ThreeBoundQ3.isGuard
                (@List.get.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts v))
              Bool.true)
            (R v w))
        (fun (a : Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts)) =>
          @instDecidableAnd
            (@Eq.{1} Bool
              (Sensitivity213981Formal.ThreeBoundQ3.isGuard
                (@List.get.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts a))
              Bool.true)
            (R a w)
            (instDecidableEqBool
              (Sensitivity213981Formal.ThreeBoundQ3.isGuard
                (@List.get.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts a))
              Bool.true)
            (inst a w))
        (@Finset.univ.{0} (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts))
          (Fin.fintype (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts))))) := by sorry
