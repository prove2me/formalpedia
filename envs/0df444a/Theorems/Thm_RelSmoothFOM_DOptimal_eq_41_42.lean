-- Prove2me | Theorems.Thm_RelSmoothFOM_DOptimal_eq_41_42
-- name    : RelSmoothFOM.DOptimal.eq_41_42
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T04:35:02.257601+00:00
-- url     : https://prove2.me/theorems/514e372e-469d-4fc7-850e-042d5eeec0b1
-- title:
--   Equations (41)–(42) — Bregman distance at the uniform start
-- statement:
--   Let $n\ge1$, $\delta>0$, $x^0=e/n$, and let $\hat x$ be a positive-simplex point with $\hat x_j\ge\delta/n$ for every coordinate. For the logarithmic barrier $h$,
--   $$D_h(\hat x,x^0)=h(\hat x)-h(x^0)\le n\log(1/\delta).$$
--   The first equality uses the zero-sum displacement from $x^0$; the bound controls the initial Bregman distance in Theorem 4.1.
--
--   **Formalization Note** The lower coordinate bound is the page's $\hat x\ge(\delta/n)e$ and prevents taking the logarithm of zero.
-- source:
--   Lu, Freund & Nesterov, Relatively smooth convex optimization by first-order methods, and applications, SIAM J. Optim. 28 (2018), p. 349, (41)–(42)

import Mathlib
import Definitions.Def_RelSmoothFOM_DOptimal_Setting

namespace RelSmoothFOM.DOptimal

/-- The Bregman identity and logarithmic estimate (41)–(42). -/
theorem eq_41_42 {n : ℕ} (hn : 1 ≤ n) (δ : ℝ) (hδ : 0 < δ)
    (xhat : Fin n → ℝ) (hh : xhat ∈ posSimplex n)
    (hlower : ∀ j, δ / (n : ℝ) ≤ xhat j) :
    let x0 : Fin n → ℝ := fun _ => 1 / (n : ℝ)
    RelSmoothFOM.PrimalGrad.bregman logBarrier xhat x0 = logBarrier xhat - logBarrier x0 ∧
      logBarrier xhat - logBarrier x0 ≤ (n : ℝ) * Real.log (1 / δ) := by sorry

end RelSmoothFOM.DOptimal
