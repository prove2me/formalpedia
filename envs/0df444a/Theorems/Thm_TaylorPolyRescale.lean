-- Prove2me | Theorems.Thm_TaylorPolyRescale
-- name    : TaylorPolyRescale
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:10:11.87094+00:00
-- url     : https://prove2.me/theorems/34af76ab-171d-4bb5-8008-80c75fc7cca0
-- title:
--   Taylor Poly Rescale: Taylor Poly Rescale
-- statement:
--   Behaviour of the Taylor data under the paper's blow-up rescaling
--   `v_L(x) = v(R x) / R^σ` with `0 < R` (paper eq:coefficients and the normalization preceding
--   eq:approximation).
--
--   Two conclusions.
--
--   1. The jet identity, in diagonal form: for every `j ≤ k` and every direction `w`,
--      `D^j v(0)[w,…,w] = R^(σ - j) · D^j v_L(0)[w,…,w]`.
--      Taking absolute values recovers the paper's eq:coefficients verbatim.  For `j ≤ k` and
--      `k < σ` the exponent `σ - j` is positive, which is what makes this a GAIN as `R → 0` and
--      is the whole point of the rescaling in the paper's iteration; the node does not need that
--      inequality and so does not assume it.
--
--   2. The polynomial identity `TaylorPoly k v 0 z = R^σ · TaylorPoly k v_L 0 (R⁻¹ • z)`, i.e. the
--      degree-`k` Taylor polynomials of `v` and of `v_L` at the origin correspond under the same
--      rescaling as the functions themselves.
--
--   The regularity hypothesis is LOCAL — `v` is only assumed `C^k` on some ball `ball 0 ρ` around
--   the origin — because that is all the consumers have: in section 3 of the paper `v` is
--   `p`-harmonic on `ball 0 1` and `C^k` only on a solution-dependent neighbourhood of a
--   non-critical point.  Mathlib's dilation rule for `iteratedFDeriv` requires global
--   `ContDiff`, so the identity is obtained instead from the within-a-set composition rule for a
--   continuous linear map, applied on `ball 0 ρ` and its preimage, both of which are open, and
--   transported to the ambient `iteratedFDeriv` there.
--
--   `v_L` is supplied as a function together with the defining equation `hvL` rather than written
--   out, so that a consumer may plug in whatever rescaled solution it has already constructed.
--
--   Conclusion 1 is DIAGONAL, and loses nothing: classically, for `j ≤ k` both
--   `iteratedFDeriv ℝ j v 0` and `iteratedFDeriv ℝ j vL 0` are SYMMETRIC, and two symmetric
--   `j`-linear forms with equal diagonal evaluations are equal by polarization, so conclusion 1 says
--   the same thing as the identity of full multilinear forms.  That is classical background about the
--   object: it is NOT a background item of this development and it is NOT a step available to any
--   proof in the tablet.  Mathlib at the pinned revision supplies symmetry of the iterated derivative
--   of a finitely smooth function only at order two, general order requiring analyticity, which is
--   why every statement here carries higher-order derivatives diagonally.
--
--   Source: https://github.com/na0b/phigherorder-lean/blob/1ab3890a96c86ab99822d51d99058a81269c2262/PHigherOrder/TaylorPolyRescale.lean#L39-L111
-- source:
--   https://github.com/na0b/phigherorder-lean/blob/1ab3890a96c86ab99822d51d99058a81269c2262/PHigherOrder/TaylorPolyRescale.lean#L39-L111

import Definitions.Def_PHigherOrder_TaylorPoly
import Definitions.Def_PHigherOrder_TaylorPolyRescale
set_option autoImplicit false

theorem TaylorPolyRescale (k : ℕ) (σ : ℝ) (v : Plane → ℝ) (ρ : ℝ) (hρ : 0 < ρ)
    (hv : ContDiffOn ℝ (k : ℕ∞) v (Metric.ball 0 ρ))
    (R : ℝ) (hR0 : 0 < R)
    (vL : Plane → ℝ) (hvL : ∀ x : Plane, vL x = v (R • x) / R ^ σ) :
    (∀ j : ℕ, j ≤ k → ∀ w : Plane,
        iteratedFDeriv ℝ j v 0 (fun _ => w)
          = R ^ (σ - (j : ℝ)) * iteratedFDeriv ℝ j vL 0 (fun _ => w))
      ∧ (∀ z : Plane, TaylorPoly k v 0 z = R ^ σ * TaylorPoly k vL 0 (R⁻¹ • z)) := by sorry
