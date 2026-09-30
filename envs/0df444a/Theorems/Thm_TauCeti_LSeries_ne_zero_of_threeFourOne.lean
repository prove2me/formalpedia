-- Prove2me | Theorems.Thm_TauCeti_LSeries_ne_zero_of_threeFourOne
-- name    : TauCeti.LSeries.ne_zero_of_threeFourOne
-- status  : Proved
-- author  : @riccardo.brasca
-- created : 2026-09-29T20:44:55.168717+00:00
-- url     : https://prove2.me/theorems/d9667ff4-41b7-4c66-b21d-846041a5bfd7
-- title:
--   The analytic 3–4–1 nonvanishing criterion
-- statement:
--   Let $f_0,f_1,f_2:\mathbb C\to\mathbb C$ and $t\in\mathbb R$. Suppose that, as the real variable $\sigma\to1^+$,
--
--   $$
--   1\le\left|f_0(\sigma)^3f_1(\sigma+it)^4f_2(\sigma+2it)\right|\quad\text{eventually},\qquad f_0(\sigma)=O((\sigma-1)^{-1}).
--   $$
--
--   If $f_1$ is complex differentiable at $1+it$ and $f_2$ is continuous at $1+2it$, then
--
--   $$
--   f_1(1+it)\ne0.
--   $$
--
--   This criterion turns the 3–4–1 product bound into nonvanishing on the boundary of a half-plane.
--
--   Source: the [Tau Ceti contributors](https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/LSeries/Nonvanishing.lean#L57-L101) (Apache-2.0, commit `948fe4751b1fe528b6d580c522ca5d743d47f185`).
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/LSeries/Nonvanishing.lean#L57-L101

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Complex.Basic

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Nonvanishing on the line `Re s = 1` from a 3-4-1 bound

The classical `3-4-1` argument proves that an `L`-series does not vanish on the line `Re s = 1`
in two steps. The first is arithmetic: an Euler product and the positivity of
`3 + 4 cos θ + cos 2θ` give, for real `σ > 1`,

```text
1 ≤ ‖L₀(σ) ^ 3 * L₁(σ + it) ^ 4 * L₂(σ + 2it)‖,
```

where `L₀` is the series of the trivial character, `L₁` that of a character `χ`, and `L₂` that of
`χ²`. The second step is analytic and uses no arithmetic: if `L₀(σ) = O((σ - 1)⁻¹)` as `σ → 1⁺`,
`L₂` stays bounded near `1 + 2it`, and `L₁` is differentiable at `1 + it` and vanishes there,
then as `σ → 1⁺` the product is `O((σ - 1)⁻³ (σ - 1)⁴) = O(σ - 1)`, contradicting the
lower bound. This file proves the second step for arbitrary functions, so that each family of
`L`-series needs to supply only its own `3-4-1` bound and its analytic inputs.

The growth condition on `f₀` is the one-sided bound `f₀(σ) = O((σ - 1)⁻¹)` as real `σ → 1⁺`.
It follows from a limit of `(σ - 1) f₀(σ)` as `σ → 1⁺`, which is how such a bound is usually
available for a Dedekind zeta function; `TauCeti.isBigO_inv_sub_one_of_tendsto_sub_one_mul`
records that implication.

## Main results

* `TauCeti.LSeries.ne_zero_of_threeFourOne`: the `3-4-1` bound together with the bound
  `f₀(σ) = O((σ - 1)⁻¹)`, differentiability of `f₁` at `1 + it` and continuity of `f₂` at
  `1 + 2it` forces `f₁ (1 + it) ≠ 0`.

## References

* H. Davenport, *Multiplicative Number Theory*, Chapter 4.
* The argument is the one in Mathlib's `Mathlib/NumberTheory/LSeries/Nonvanishing.lean`, by
  Michael Stoll and David Loeffler, where the private lemma
  `DirichletCharacter.LFunction_ne_zero_of_not_quadratic_or_ne_one` carries it out for Dirichlet
  `L`-functions. Here it is separated from the Dirichlet characters.
-/

 section

namespace TauCeti.LSeries
end TauCeti.LSeries
section TauCeti.LSeries
open TauCeti TauCeti.LSeries

open Asymptotics Complex Filter
open scoped Topology

theorem TauCeti.LSeries.ne_zero_of_threeFourOne {f₀ f₁ f₂ : ℂ → ℂ} {t : ℝ}
    (hbound : ∀ᶠ σ : ℝ in 𝓝[>] 1,
      1 ≤ ‖f₀ σ ^ 3 * f₁ (σ + _root_.Complex.I * t) ^ 4 * f₂ (σ + 2 * _root_.Complex.I * t)‖)
    (h₀ : (fun σ : ℝ ↦ f₀ σ) =O[𝓝[>] 1] fun σ : ℝ ↦ (σ - 1)⁻¹)
    (h₁ : _root_.DifferentiableAt ℂ f₁ (1 + _root_.Complex.I * t)) (h₂ : _root_.ContinuousAt f₂ (1 + 2 * _root_.Complex.I * t)) :
    f₁ (1 + _root_.Complex.I * t) ≠ 0 := by sorry
