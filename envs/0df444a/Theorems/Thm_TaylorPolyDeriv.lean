-- Prove2me | Theorems.Thm_TaylorPolyDeriv
-- name    : TaylorPolyDeriv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:10:09.663395+00:00
-- url     : https://prove2.me/theorems/2949b4ea-5722-40e2-8cfd-2dce067aec83
-- title:
--   Taylor Poly Deriv: Taylor Poly Deriv
-- statement:
--   The five facts about `TaylorPoly k u x₀` that section 3 of the paper uses.  Writing
--   `P = TaylorPoly k u x₀`:
--
--   1. `P` is smooth;
--   2. `D^(k+1) P ≡ 0`, i.e. `P` is a polynomial of degree at most `k` — this is exactly the
--      hypothesis of `PolyInverseEstimate`;
--   3. at order exactly `k` the diagonal evaluations of `D^k P` are those of `D^k u(x₀)`, AT EVERY
--      POINT `z`, not only at the centre — this is what lets `PolyInverseEstimate` be applied to a
--      difference `TaylorPoly k u x - TaylorPoly k u y` of two Taylor polynomials and return
--      `D^k u(x)[w,…,w] - D^k u(y)[w,…,w]`;
--   4. at the centre `x₀` the diagonal evaluations of `D^j P` are those of `D^j u(x₀)` for every
--      `j ≤ k` (paper eq:coefficients);
--   5. `P(x₀) = u(x₀)`.
--
--   No regularity whatsoever is assumed of `u`: `TaylorPoly` is built out of the fixed continuous
--   multilinear forms `D^j u(x₀)`, and all five conclusions are unconditional identities about the
--   resulting polynomial.
--
--   Conclusions 3 and 4 are stated DIAGONALLY and cannot be strengthened to the full multilinear
--   form: `D^k P(z)` equals `k!` times the SYMMETRIZATION of `D^k u(x₀)`, not that form itself, and
--   the symmetrization is recovered only on the diagonal.  Classically, when `u` is of class `C^k`
--   near `x₀` the form `D^k u(x₀)` is symmetric, and on a symmetric form the diagonal evaluations
--   determine the form while the diagonal supremum is equivalent to the operator norm with constants
--   depending only on `k`, so for such `u` nothing is lost.  That is classical background about the
--   object: it is NOT a background item of this development and it is NOT a step available to any
--   proof in the tablet.  Mathlib at the pinned revision supplies symmetry of the iterated
--   derivative of a finitely smooth function only at order two.
--
--   Source: https://github.com/na0b/phigherorder-lean/blob/1ab3890a96c86ab99822d51d99058a81269c2262/PHigherOrder/TaylorPolyDeriv.lean#L30-L156
-- source:
--   https://github.com/na0b/phigherorder-lean/blob/1ab3890a96c86ab99822d51d99058a81269c2262/PHigherOrder/TaylorPolyDeriv.lean#L30-L156

import Definitions.Def_PHigherOrder_TaylorPoly
import Definitions.Def_PHigherOrder_TaylorPolyDeriv
set_option autoImplicit false

theorem TaylorPolyDeriv (k : ℕ) (u : Plane → ℝ) (x₀ : Plane) :
    ContDiff ℝ (⊤ : ℕ∞) (TaylorPoly k u x₀)
      ∧ (∀ z : Plane, iteratedFDeriv ℝ (k + 1) (TaylorPoly k u x₀) z = 0)
      ∧ (∀ z w : Plane, iteratedFDeriv ℝ k (TaylorPoly k u x₀) z (fun _ => w)
            = iteratedFDeriv ℝ k u x₀ (fun _ => w))
      ∧ (∀ j : ℕ, j ≤ k → ∀ w : Plane,
            iteratedFDeriv ℝ j (TaylorPoly k u x₀) x₀ (fun _ => w)
              = iteratedFDeriv ℝ j u x₀ (fun _ => w))
      ∧ TaylorPoly k u x₀ x₀ = u x₀ := by sorry
