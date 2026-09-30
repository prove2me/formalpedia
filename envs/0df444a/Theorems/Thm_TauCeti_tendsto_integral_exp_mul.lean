-- Prove2me | Theorems.Thm_TauCeti_tendsto_integral_exp_mul
-- name    : TauCeti.tendsto_integral_exp_mul
-- status  : Proved
-- author  : @riccardo.brasca
-- created : 2026-09-29T20:46:20.886976+00:00
-- url     : https://prove2.me/theorems/4130a3e5-e5d0-4b73-914a-1d660aea702a
-- title:
--   Convergence of a damped half-line Laplace integral
-- statement:
--   Let $x>0$ and let $f:\mathbb R\to\mathbb C$ be integrable on $[-\log x,\infty)$. As the real parameter $\sigma$ approaches one from above,
--
--   $$
--   x^{1-\sigma}\int_{-\log x}^{\infty}e^{-u(\sigma-1)}f(u)\,du\longrightarrow\int_{-\log x}^{\infty}f(u)\,du.
--   $$
--
--   The normalized damped integral recovers the undamped half-line integral at the boundary.
--
--   Source and proof credit: the Tau Ceti contributors, [original declaration and proof](https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/MeasureTheory/Integral/ExpDamped.lean#L51-L80), Apache-2.0, commit `948fe4751b1fe528b6d580c522ca5d743d47f185`; adapted to Lean 4.33.1.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/MeasureTheory/Integral/ExpDamped.lean#L51-L80

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.DominatedConvergence

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Vanishing exponential damping of a half-line integral

Damping an integrand on the half-line `u ≥ -log x` by `exp (-u (sigma - 1))` and normalizing by
`x ^ (1 - sigma)`, the reciprocal of the damping at the left endpoint, leaves the integral of
an integrable function unchanged in the limit `sigma → 1⁺`: the damping factor is bounded on
the half-line uniformly in `sigma ∈ (1, 2]`, so dominated convergence applies.

This is the Abelian step of a Tauberian argument, where a Dirichlet series is tested on a vertical
line `Re s = sigma` inside its half-plane of convergence and the line is pushed to the boundary;
`TauCeti.LSeries.tsum_term_mul_fourier_sub_pole_eq_integral_boundary` uses it for the simple-pole
term of the Wiener--Ikehara identity.

## Main results

* `TauCeti.tendsto_integral_exp_mul`: the normalized damped integral converges to the undamped
  one as `sigma` decreases to `1`.
-/

 section

namespace TauCeti
end TauCeti
section TauCeti
open TauCeti

open Filter MeasureTheory Set
open scoped Topology

variable {f : ℝ → ℂ} {x : ℝ}

theorem TauCeti.tendsto_integral_exp_mul (hx : 0 < x) (hf : _root_.MeasureTheory.IntegrableOn f (_root_.Set.Ici (-_root_.Real.log x))) :
    _root_.Filter.Tendsto (fun sigma : ℝ ↦ ((x ^ (1 - sigma) : ℝ) : ℂ) *
        ∫ u in _root_.Set.Ici (-_root_.Real.log x), (_root_.Real.exp (-u * (sigma - 1)) : ℂ) * f u)
      (𝓝[>] 1) (𝓝 (∫ u in _root_.Set.Ici (-_root_.Real.log x), f u)) := by sorry
