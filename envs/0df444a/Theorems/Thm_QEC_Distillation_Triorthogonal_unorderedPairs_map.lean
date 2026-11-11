-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_unorderedPairs_map
-- name    : QEC.Distillation.Triorthogonal.unorderedPairs_map
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T12:34:52.293855+00:00
-- url     : https://prove2.me/theorems/4d3dcb48-51e1-4c50-b9d8-fdf52ff9882e
-- title:
--   Triorthogonal: unordered Pairs map
-- statement:
--   The Triorthogonal construction uses the unordered Pairs map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Transversal.lean#L597-L603
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Transversal.lean#L597-L603

import Definitions.Def_QEC_Distillation_Triorthogonal_CSS
import Definitions.Def_QEC_Distillation_Triorthogonal_Transversal
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.Triorthogonal
open Semantics
open Coding
open Coding.PauliSymplectic
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
universe u
variable {Index : Type u} [Fintype Index] [DecidableEq Index]

theorem QEC.Distillation.Triorthogonal.unorderedPairs_map {A B : Type*} (f : A → B) (xs : List A) :
    unorderedPairs (xs.map f) =
      (unorderedPairs xs).map fun pq => (f pq.1, f pq.2) := by sorry
