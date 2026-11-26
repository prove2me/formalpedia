-- Prove2me | Theorems.Thm_Sendov_natDegree_rotate
-- name    : Sendov.natDegree_rotate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T20:06:14.57619+00:00
-- url     : https://prove2.me/theorems/4c7ad42b-c346-49f1-933e-6d73ab2e641a
-- title:
--   Sendov: nat Degree rotate
-- statement:
--   The Sendov construction uses the nat Degree rotate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Conjecture.lean#L49-L51
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Conjecture.lean#L49-L51

import Definitions.Def_Sendov_Interior
import Definitions.Def_Sendov_Boundary
import Definitions.Def_Sendov_Conjecture
set_option autoImplicit false
open Sendov
open Polynomial

theorem Sendov.natDegree_rotate {ω : ℂ} (hω : ω ≠ 0) (p : ℂ[X]) :
    (rotate ω p).natDegree = p.natDegree := by sorry
