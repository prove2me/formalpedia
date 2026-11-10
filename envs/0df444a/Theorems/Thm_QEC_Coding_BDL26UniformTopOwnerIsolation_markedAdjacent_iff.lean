-- Prove2me | Theorems.Thm_QEC_Coding_BDL26UniformTopOwnerIsolation_markedAdjacent_iff
-- name    : QEC.Coding.BDL26UniformTopOwnerIsolation.markedAdjacent_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:19:26.418204+00:00
-- url     : https://prove2.me/theorems/3194040c-a1a8-4f2e-b755-f6d8700ca41f
-- title:
--   BDL26 Uniform Top Owner Isolation: marked Adjacent iff
-- statement:
--   The BDL26 Uniform Top Owner Isolation construction uses the marked Adjacent iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformIsolation.lean#L27-L29
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformIsolation.lean#L27-L29

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TopOwnerIsolation
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformIsolation
import Theorems.Thm_QEC_Coding_BDL26TopOwnerIsolation_markedAdjacent_iff
attribute [local simp] QEC.Coding.BDL26TopOwnerIsolation.markedAdjacent_iff


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26UniformTopOwnerIsolation
open BDL26FiniteTannerSquare BDL26DecodingGraph MultiscaleDecoder
open scoped Classical

theorem QEC.Coding.BDL26UniformTopOwnerIsolation.markedAdjacent_iff (S : OddScale) (n : Nat) (M : Finset (Node S n))
    (u v : {w : Node S n // w ∈ M}) :
    markedAdjacent S n M u v ↔ (graph S n).adjacent u.val v.val := by sorry
