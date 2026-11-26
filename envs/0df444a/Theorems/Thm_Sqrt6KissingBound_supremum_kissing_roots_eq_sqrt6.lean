-- Prove2me | Theorems.Thm_Sqrt6KissingBound_supremum_kissing_roots_eq_sqrt6
-- name    : Sqrt6KissingBound.supremum_kissing_roots_eq_sqrt6
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:24:55.631199+00:00
-- url     : https://prove2.me/theorems/a2a93490-ea12-44fb-98e3-0a02dec84361
-- title:
--   Sqrt6 Kissing Bound: supremum kissing roots eq sqrt6
-- statement:
--   The Sqrt6 Kissing Bound construction uses the supremum kissing roots eq sqrt6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Sqrt6KissingBound/Optimality.lean#L142-L162
-- source:
--   https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Sqrt6KissingBound/Optimality.lean#L142-L162

import Definitions.Def_Sqrt6KissingBound_KissingBound
import Definitions.Def_Sqrt6KissingBound_StandardGeometry
import Definitions.Def_Sqrt6KissingBound_Optimality
set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section

theorem Sqrt6KissingBound.supremum_kissing_roots_eq_sqrt6 :
    sSup {x : ℝ | ∃ n : ℕ, 1 ≤ n ∧ ∃ X : Finset (EuclideanSpace ℝ (Fin n)),
      IsKissingConfiguration X ∧ x = (X.card : ℝ) ^ ((n : ℝ)⁻¹)} =
      Real.sqrt 6 := by sorry
