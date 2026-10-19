-- Prove2me | Theorems.Thm_Relation_RelatesInSteps_succ_iff
-- name    : Relation.RelatesInSteps.succ_iff
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T00:19:33.817377+00:00
-- url     : https://prove2.me/theorems/f3d6b619-b0e6-45c7-869e-eed25b1641a3
-- title:
--   Lemma succ_iff of the MIP* = RE formalization
-- statement:
--   A statement of the module `MIPRE.Cslib.Foundations.Data.RelatesInSteps` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Relations Across Steps. This file defines `Relation.RelatesInSteps` (and `Relation.RelatesWithinSteps`). These are inductively defines propositions that communicate whether a relation forms a chain of length `n` (or at most `n`) between two elements.
--
--   The module is vendored from [CSLib](https://github.com/leanprover/cslib) (commit `3aa9d441`, 2026-08-03; Apache 2.0): upstream file `Cslib/Foundations/Data/RelatesInSteps.lean`, by Bolton Bailey; the file header lists the adaptations. The declarations, statements and proofs are upstream's, not this repository's.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open Relation
--   open Relation.RelatesInSteps
--   variable {α : Type*} {r : α → α → Prop} {a b c : α}
--
--   theorem Relation.RelatesInSteps.succ_iff {a b : α} {n : ℕ} :
--       RelatesInSteps r a b (n + 1) ↔ ∃ t', RelatesInSteps r a t' n ∧ r t' b
--   ```
--
--   **Formalization Note** `Relation.RelatesInSteps.succ_iff` is declared in `MIPRE/Cslib/Foundations/Data/RelatesInSteps.lean`, lines 116–121. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Cslib/Foundations/Data/RelatesInSteps.lean#L116-L121

import Mathlib.Data.Nat.Notation
import Mathlib.Logic.Relation
import Definitions.Def_MIPRE_Cslib_Foundations_Data_RelatesInSteps

open Relation
open Relation.RelatesInSteps
set_option autoImplicit true
set_option relaxedAutoImplicit true
variable {α : Type*} {r : α → α → Prop} {a b c : α}

theorem Relation.RelatesInSteps.succ_iff {a b : α} {n : ℕ} :
    RelatesInSteps r a b (n + 1) ↔ ∃ t', RelatesInSteps r a t' n ∧ r t' b := by sorry
