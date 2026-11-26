-- Prove2me | Theorems.Thm_Sendov_exists_crit_multiset
-- name    : Sendov.exists_crit_multiset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:56:47.466814+00:00
-- url     : https://prove2.me/theorems/103ae7ca-b3c6-5746-8424-63a7191842c6
-- title:
--   Sendov: exists crit multiset
-- statement:
--   The factorization of `p'`.  Each critical point `w` lies at distance at least `1` from `a`,
--   so `(a - w)⁻¹` lies in the closed unit disk and `w = a - ((a-w)⁻¹)⁻¹`.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Counterexample/Factor.lean#L74-L131
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Counterexample/Factor.lean#L74-L131

import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Analysis.Complex.Basic
import Definitions.Def_Sendov_Counterexample_Factor
set_option autoImplicit false
open Sendov
open Polynomial

theorem Sendov.exists_crit_multiset {n : ℕ} (hn : 2 ≤ n) {p : ℂ[X]} (hdeg : p.natDegree = n) {a : ℂ}
    (hcrit : ∀ w : ℂ, (derivative p).eval w = 0 → 1 ≤ ‖w - a‖) :
    ∃ q : Multiset ℂ, q.card = n - 1 ∧ (∀ v ∈ q, ‖v‖ ≤ 1) ∧ (∀ v ∈ q, v ≠ 0) ∧
      derivative p = C ((n : ℂ) * p.leadingCoeff)
        * (q.map (fun v => X - C (a - v⁻¹))).prod := by sorry
