-- Prove2me | Theorems.Thm_WLight_frickeFunction_orbit_package
-- name    : WLight.frickeFunction_orbit_package
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.37934+00:00
-- url     : https://prove2.me/theorems/31f08140-fc87-5825-b66a-596acddc0651
-- title:
--   Polar growth of j and Fricke functions, and their orbit polynomial
-- statement:
--   Let $N$ be a nonzero natural number. Let $L$ assign to each point $\tau$ of the upper half-plane a period pair, pinned by the hypothesis that its first period is $\tau$ and its second period is $1$. Let $W$ be a family of functions on the upper half-plane indexed by $v \in (\mathbb{Z}/N)^2$, pinned by $W_v(\tau) = (2\pi i)^{-2}\,\wp_{L(\tau)}\big((\tilde v_0 \tau + \tilde v_1)/N\big)$, where $\tilde v_i$ denotes the canonical representative in $\{0,\dots,N-1\}$ of $v_i$ and $\wp$ is the Weierstrass function of the period pair; let $\mathrm{fricke}$ be pinned by $\mathrm{fricke}_v(\tau) = -\big(E_4(\tau)E_6(\tau)/\Delta(\tau)\big)/2592 \cdot W_v(\tau)$; and let $jf$ be pinned by $jf(\tau) = E_4(\tau)^3/\Delta(\tau)$. The conclusion is a threefold conjunction: (i) $jf$ is holomorphic on the upper half-plane and there is an $m \in \mathbb{N}$ with $jf \cdot \Delta^m$ bounded at $i\infty$; (ii) for every $v \neq 0$, $\mathrm{fricke}_v$ is holomorphic and there is an $m \in \mathbb{N}$ with $\mathrm{fricke}_v \cdot \Delta^m$ bounded at $i\infty$; (iii) there is a family of polynomials $P_k \in \mathbb{C}[X]$, $k \in \mathbb{N}$, all of whose coefficients lie in the subfield $\mathbb{Q}(e^{2\pi i/N})$ of $\mathbb{C}$, such that for every $v \neq 0$ and every $\tau$, $\mathrm{fricke}_v(\tau)^{N^2-1} + \sum_{k<N^2-1} P_k(jf(\tau))\,\mathrm{fricke}_v(\tau)^k = 0$; that is, a single monic relation of degree $N^2-1$ over $\mathbb{C}[jf]$, with coefficient polynomials having cyclotomic coefficients, annihilates all the Fricke functions of nonzero index simultaneously.
--
--   This is the integrality statement for the Fricke functions of level $N$: the $N^2-1$ functions of nonzero index form a single orbit under the index action of the modular group, so the elementary symmetric functions of the orbit are level-one invariants of finite polar growth and hence polynomials in $j$, with coefficients in $\mathbb{Q}(e^{2\pi i/N})$. It is used in the construction of the function field of the modular curve of level $N$ and of its $q$-expansion and valuation data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WLight_frickeFunction_orbit_package.lean

import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic
import Mathlib.NumberTheory.ModularForms.Discriminant
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
import Mathlib.Geometry.Manifold.Notation
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open Complex Real UpperHalfPlane
open scoped Manifold MatrixGroups ModularForm

theorem WLight.frickeFunction_orbit_package
    (N : ℕ) [NeZero N]
    (L : ℍ → PeriodPair) (hL : ∀ τ : ℍ, (L τ).ω₁ = (τ : ℂ) ∧ (L τ).ω₂ = 1)
    (W : (Fin 2 → ZMod N) → ℍ → ℂ)
    (hW : ∀ (v : Fin 2 → ZMod N) (τ : ℍ), W v τ = ((2 * (Real.pi : ℂ) * Complex.I) ^ 2)⁻¹ *
      PeriodPair.weierstrassP (L τ) ((((v 0).val : ℂ) * (τ : ℂ) + ((v 1).val : ℂ)) / (N : ℂ)))
    (fricke : (Fin 2 → ZMod N) → ℍ → ℂ)
    (hfricke : ∀ (v : Fin 2 → ZMod N) (τ : ℍ), fricke v τ =
      -(ModularForm.E₄ τ * ModularForm.E₆ τ / ModularForm.discriminant τ) / 2592 * W v τ)
    (jf : ℍ → ℂ)
    (hjf : ∀ τ : ℍ, jf τ = ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ) :

    (MDifferentiable 𝓘(ℂ) 𝓘(ℂ) jf ∧
      ∃ m : ℕ, IsBoundedAtImInfty (jf * ModularForm.discriminant ^ m)) ∧

    (∀ v : Fin 2 → ZMod N, v ≠ 0 → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fricke v) ∧
      ∃ m : ℕ, IsBoundedAtImInfty (fricke v * ModularForm.discriminant ^ m)) ∧

    (∃ P : ℕ → Polynomial ℂ,
      (∀ k i, (P k).coeff i ∈
        IntermediateField.adjoin ℚ {Complex.exp (2 * (Real.pi : ℂ) * Complex.I / N)}) ∧
      ∀ v : Fin 2 → ZMod N, v ≠ 0 → ∀ τ : ℍ,
        fricke v τ ^ (N ^ 2 - 1) + ∑ k ∈ Finset.range (N ^ 2 - 1),
          (P k).eval (jf τ) * fricke v τ ^ k = 0) := by sorry
