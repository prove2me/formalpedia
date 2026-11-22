-- Prove2me | Theorems.Thm_TaylorPolyAffine
-- name    : TaylorPolyAffine
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:13:55.1588+00:00
-- url     : https://prove2.me/theorems/45ae8fd2-6468-43fb-8080-7dbac0d151fc
-- title:
--   Taylor Poly Affine: Taylor Poly Affine
-- statement:
--   Transport of the degree-`k` Taylor polynomial through the paper's affine normalization
--   `w y = (u (x₀ + r • y) - u x₀) / M`, which carries a translation, an additive constant and a
--   dilation at once.
--
--   This is the Taylor-side counterpart of `PHarmNormalize`: that node transports `p`-harmonicity
--   through the same substitution, and nothing transported the Taylor polynomial.
--   `TaylorPolyRescale` does not cover it — it is centred at the origin, has no additive constant,
--   and scales by `R^sigma` rather than by a free constant `M`.  The paper needs exactly this at
--   lines 283-295, where `w_x y = (u (x + y/4) - u x)/M_0` and `P_x(z) = u(x) + M_0 Q_x(4(z-x))`
--   with `Q_x` the Taylor polynomial of `w_x` at zero.
--
--   Two conclusions.  (1) The jet identity, diagonally: for `1 ≤ j ≤ k`,
--   `D^j w(0)[e,…,e] = (r^j / M) · D^j u(x₀)[e,…,e]`.  The restriction to `j ≥ 1` is necessary and
--   not a weakness: at `j = 0` the additive constant does not cancel, and indeed `w 0 = 0` while
--   `u x₀` need not vanish.  (2) The polynomial identity
--   `TaylorPoly k u x₀ z = u x₀ + M · TaylorPoly k w 0 (r⁻¹ • (z - x₀))`, which is the paper's
--   `P_x` formula; the additive `u x₀` is exactly the degree-zero term that (1) omits.
--
--   The regularity hypothesis is LOCAL, `C^k` on a single ball about `x₀`, which is all the
--   consumers have.  Only the dilation needs the within-a-set composition rule for a continuous
--   linear map; the translation is unconditional.
--
--   Source: https://github.com/na0b/phigherorder-lean/blob/1ab3890a96c86ab99822d51d99058a81269c2262/PHigherOrder/TaylorPolyAffine.lean#L24-L125
-- source:
--   https://github.com/na0b/phigherorder-lean/blob/1ab3890a96c86ab99822d51d99058a81269c2262/PHigherOrder/TaylorPolyAffine.lean#L24-L125

import Definitions.Def_PHigherOrder_TaylorPolyRescale
import Definitions.Def_PHigherOrder_TaylorPolyAffine
import Theorems.Thm_TaylorPolyRescale

set_option autoImplicit false

theorem TaylorPolyAffine (k : ℕ) (u : Plane → ℝ) (x₀ : Plane) (ρ : ℝ) (hρ : 0 < ρ)
    (hu : ContDiffOn ℝ (k : ℕ∞) u (Metric.ball x₀ ρ))
    (r : ℝ) (hr : 0 < r) (M : ℝ) (hM : 0 < M)
    (w : Plane → ℝ) (hw : ∀ y : Plane, w y = (u (x₀ + r • y) - u x₀) / M) :
    (∀ j : ℕ, 1 ≤ j → j ≤ k → ∀ e : Plane,
        iteratedFDeriv ℝ j w 0 (fun _ => e)
          = (r ^ j / M) * iteratedFDeriv ℝ j u x₀ (fun _ => e))
      ∧ (∀ z : Plane, TaylorPoly k u x₀ z = u x₀ + M * TaylorPoly k w 0 (r⁻¹ • (z - x₀))) := by sorry
