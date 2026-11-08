-- Prove2me | Theorems.Thm_UniversalSubmod_lattice_count
-- name    : UniversalSubmod.lattice_count
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:51:34.859209+00:00
-- url     : https://prove2.me/theorems/5105583a-3300-4b70-9923-44a0280e3075
-- title:
--   Lattice-point display, §4.3, p.14 — $|\{y\in\mathbb Z^k:\|y\|\le\rho\}|\le(2\rho\sqrt{2\pi e/k})^k$ for $\rho\ge\sqrt k/2$
-- statement:
--   Let $k\ge1$ and let $\rho$ be a radius with $\sqrt k/2+\rho\le2\rho$, i.e. $\rho\ge\sqrt k/2$. The set of lattice points $\{y\in\mathbb Z^k:\|y\|\le\rho\}$ is finite, and
--   $$
--   \big|\{y\in\mathbb Z^k:\|y\|\le\rho\}\big|\ \le\ (2\rho)^k\int_{\mathbb R^k}\mathbf 1\{\|y\|\le1\}\,dy\ \le\ (2\rho)^k\int_{\mathbb R^k}e^{k(1-\|y\|^2)/2}\,dy\ =\ \Big(2\rho\sqrt{\tfrac{2\pi e}{k}}\Big)^k .
--   $$
--   In the proof of Theorem 1.1 this is applied with $\rho=r/\eta$, $r=\sqrt{2k/\eta}$; it bounds the number of grid normals, and hence the size of the universal family.
--
--   **Formalization Note** Lattice points are $y:\{1,\dots,k\}\to\mathbb Z$ with $\sum_iy_i^2\le\rho^2$; the set is shown finite, so `Set.ncard` is its cardinality. Integrals are Lebesgue integrals over `EuclideanSpace ℝ (Fin k)`; the first integral is the volume of the closed unit ball. The chain is stated link by link; the middle link is divided by $(2\rho)^k>0$.
--
--   Differences from the source:
--   - generalization: the radius $r/\eta$ with $r=\sqrt{2k/\eta}$, $\eta=\varepsilon/3$ → every radius $\rho$ with $\sqrt k/2\le\rho$; reason: the display uses only $\sqrt k/2+r/\eta\le2r/\eta$, which the paper's radius satisfies, so the statement specializes to it
--   - encoding: $|\{y\in\mathbb Z^k:\|y\|\le r/\eta\}|$ → finiteness and `Set.ncard` of $\{y:$ `Fin k → ℤ` $\mid\sum_i y_i^2\le\rho^2\}$; reason: the same set ($\rho\ge0$); finiteness makes `ncard` the true count
--   - encoding: $(2\rho)^k\int\mathbf 1\{\|y\|\le1\}\le(2\rho)^k\int e^{k(1-\|y\|^2)/2}$ → $\mathrm{vol}(B_1)\le\int e^{k(1-\|y\|^2)/2}$; reason: the common factor $(2\rho)^k>0$ is divided out
--   - encoding: $\int_{\mathbb R^k}\mathbf 1\{\|y\|\le1\}\,dy$ over $\mathbb R^k$ → `(volume (Metric.closedBall 0 1)).toReal` on `EuclideanSpace ℝ (Fin k)`; reason: the integral of an indicator is the volume of the set, which is finite; Lebesgue measure on `EuclideanSpace` gives the unit cube volume 1
-- source:
--   Adamczyk, Ueltzen, Vondrák, Optimal universal sets for submodular functions, manuscript (Nov. 3, 2026; sha256 8a53c0912e8ad39b1019cbabfbde98980fd3eea456a8c7e5b28eb55d58343714), §4.3, display on p.14 (proof of Theorem 1.1)

import Mathlib

namespace UniversalSubmod

open MeasureTheory

/-- **Lattice-point count in a Euclidean ball** (Adamczyk, Ueltzen, Vondrák, *Optimal universal
sets for submodular functions*, manuscript of November 3, 2026, §4.3, display on p.14, in the
proof of Theorem 1.1). For the radius `ρ = r/η`, using `√k/2 + ρ ≤ 2ρ`,
`|{y ∈ ℤ^k : ‖y‖ ≤ ρ}| ≤ (2ρ)^k ∫ 1{‖y‖ ≤ 1} dy ≤ (2ρ)^k ∫ e^{k(1 − ‖y‖²)/2} dy
= ((2ρ) √(2πe/k))^k`.

**Formalization Note.** Stated for every `k ≥ 1` and every radius `ρ` with `√k/2 ≤ ρ` (the
condition `√k/2 + ρ ≤ 2ρ` the display uses); the paper's `ρ = r/η` with `r = √(2k/η)` satisfies it.
Lattice points are `y : Fin k → ℤ` with `∑ yᵢ² ≤ ρ²`. The set is shown finite, so `Set.ncard` is
its true cardinality. Integrals are over `EuclideanSpace ℝ (Fin k)` with Lebesgue measure; the
first integral is the volume of the closed unit ball. The chain is stated link by link. -/
theorem lattice_count (k : ℕ) (hk : 1 ≤ k) (ρ : ℝ) (hρ : Real.sqrt k / 2 ≤ ρ) :
    let B : Set (Fin k → ℤ) := {y | ∑ i, ((y i : ℤ) : ℝ) ^ 2 ≤ ρ ^ 2}
    B.Finite ∧
    (B.ncard : ℝ) ≤
      (2 * ρ) ^ k * (volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) 1)).toReal ∧
    (volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) 1)).toReal ≤
      ∫ y : EuclideanSpace ℝ (Fin k), Real.exp ((k : ℝ) * (1 - ‖y‖ ^ 2) / 2) ∧
    (2 * ρ) ^ k * ∫ y : EuclideanSpace ℝ (Fin k), Real.exp ((k : ℝ) * (1 - ‖y‖ ^ 2) / 2) =
      (2 * ρ * Real.sqrt (2 * Real.pi * Real.exp 1 / k)) ^ k := by sorry

end UniversalSubmod
