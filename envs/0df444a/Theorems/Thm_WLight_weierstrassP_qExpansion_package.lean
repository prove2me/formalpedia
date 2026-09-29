-- Prove2me | Theorems.Thm_WLight_weierstrassP_qExpansion_package
-- name    : WLight.weierstrassP_qExpansion_package
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.868498+00:00
-- url     : https://prove2.me/theorems/cb820829-eaed-5178-8fab-60e3462d9566
-- title:
--   Lipschitz's formula and the q-expansion of wp at torsion points
-- statement:
--   A closed conjunction of five analytic statements, where `PeriodPair` is the structure carrying periods `ω₁`, `ω₂` and `PeriodPair.weierstrassP` is the associated Weierstrass $\wp$-function. (i) For $w\in\mathbb{C}$ with $\operatorname{Im} w>0$, $\sum_{n\in\mathbb{Z}}(w+n)^{-2}=(2\pi i)^2\sum_{m\ge 0}m\,e^{2\pi i m w}$. (ii) The same for $\operatorname{Im} w<0$ with $e^{-2\pi i w}$ in place of $e^{2\pi i w}$. (iii) For $z,\tau\in\mathbb{C}$ with $-\operatorname{Im}\tau<\operatorname{Im} z<\operatorname{Im}\tau$ and $z$ in `Complex.integerComplement`, the sum over $c\in\mathbb{Z}$ of $\sum_{d\in\mathbb{Z}}(z-c\tau+d)^{-2}-\sum_{d\in\mathbb{Z}}(c\tau+d)^{-2}$ equals $(2\pi i)^2\bigl(\omega(1-\omega)^{-2}+\tfrac1{12}+\sum_{c\ge 1}\sum_{m\ge 0}m(\omega^m+\omega^{-m}-2)q^{cm}\bigr)$, with $\omega=e^{2\pi i z}$, $q=e^{2\pi i\tau}$. (iv) For every $L:\mathbb{H}\to$ `PeriodPair` with $(L\tau).\omega_1=\tau$, $(L\tau).\omega_2=1$, and all naturals $N,a_1,a_2$ with $a_1,a_2<N$ and $a_1\ne 0$ or $a_2\ne 0$: $\wp_{L\tau}((a_1\tau+a_2)/N)$ is given by the stated double series in $\zeta_N=e^{2\pi i/N}$ and $q_N=e^{2\pi i\tau/N}$ summed over $\mathbb{N}_{>0}\times\mathbb{N}_{>0}$ (the second exponent using truncated subtraction $p_1N-a_1$), and $\tau\mapsto\wp_{L\tau}((a_1\tau+a_2)/N)$ is differentiable on $\mathbb{H}$ as a map of complex manifolds. (v) For `PeriodPair`s $L,L'$ and $c\in\mathbb{C}$ with $L'.\omega_1=cL.\omega_1$ and $L'.\omega_2=cL.\omega_2$, one has $\wp_{L'}(cz)=c^{-2}\wp_L(z)$ for all $z$; no hypothesis $c\neq 0$ is imposed.
--
--   Parts (i)–(ii) are Lipschitz's (Eisenstein's) formula in weight $2$, (iii) the resulting strip expansion of $\wp_{(\tau,1)}(z)-$ its constant term, (iv) its specialisation to $N$-torsion points together with holomorphy in $\tau$, and (v) the degree $-2$ homogeneity of $\wp$ under scaling of the period pair. It is the analytic input for the $q$-expansions of the Fricke functions, used by the statements producing modular forms whose $q$-expansion coefficients match those of Fricke functions substituted into the Tate curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WLight_weierstrassP_qExpansion_package.lean

import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
import Mathlib.Analysis.Complex.IntegerCompl
import Mathlib.Geometry.Manifold.Notation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open Complex Real
open scoped UpperHalfPlane Manifold

theorem WLight.weierstrassP_qExpansion_package :

    (∀ w : ℂ, 0 < w.im →
      ∑' n : ℤ, 1 / (w + n) ^ 2 =
        (2 * π * I) ^ 2 * ∑' m : ℕ, (m : ℂ) * cexp (2 * π * I * w) ^ m) ∧

    (∀ w : ℂ, w.im < 0 →
      ∑' n : ℤ, 1 / (w + n) ^ 2 =
        (2 * π * I) ^ 2 * ∑' m : ℕ, (m : ℂ) * cexp (-(2 * π * I * w)) ^ m) ∧

    (∀ z τ : ℂ, -τ.im < z.im → z.im < τ.im → z ∈ Complex.integerComplement →
      ∑' c : ℤ, ((∑' d : ℤ, 1 / ((z - c * τ) + d) ^ 2) - ∑' d : ℤ, 1 / (c * τ + d) ^ 2) =
        (2 * π * I) ^ 2 *
          (cexp (2 * π * I * z) / (1 - cexp (2 * π * I * z)) ^ 2 + 1 / 12 +
            ∑' c : ℕ+, ∑' m : ℕ, (m : ℂ) *
              (cexp (2 * π * I * z) ^ m + (cexp (2 * π * I * z))⁻¹ ^ m - 2) *
                cexp (2 * π * I * τ) ^ ((c : ℕ) * m))) ∧

    (∀ L : ℍ → PeriodPair, (∀ τ : ℍ, (L τ).ω₁ = (τ : ℂ) ∧ (L τ).ω₂ = 1) →
      ∀ N a₁ a₂ : ℕ, a₁ < N → a₂ < N → (a₁ ≠ 0 ∨ a₂ ≠ 0) →
        (∀ τ : ℍ, PeriodPair.weierstrassP (L τ) (((a₁ : ℂ) * τ + a₂) / N) =
          (2 * π * I) ^ 2 *
            (cexp (2 * π * I / N) ^ a₂ * cexp (2 * π * I * (τ : ℂ) / N) ^ a₁ /
                (1 - cexp (2 * π * I / N) ^ a₂ * cexp (2 * π * I * (τ : ℂ) / N) ^ a₁) ^ 2 +
              1 / 12 +
              ∑' p : ℕ+ × ℕ+, ((p.2 : ℕ) : ℂ) *
                (cexp (2 * π * I / N) ^ (a₂ * (p.2 : ℕ)) *
                    cexp (2 * π * I * (τ : ℂ) / N) ^ (((p.1 : ℕ) * N + a₁) * (p.2 : ℕ)) +
                  (cexp (2 * π * I / N))⁻¹ ^ (a₂ * (p.2 : ℕ)) *
                    cexp (2 * π * I * (τ : ℂ) / N) ^ (((p.1 : ℕ) * N - a₁) * (p.2 : ℕ)) -
                  2 * cexp (2 * π * I * (τ : ℂ) / N) ^ ((p.1 : ℕ) * N * (p.2 : ℕ))))) ∧
        MDifferentiable 𝓘(ℂ) 𝓘(ℂ)
          (fun τ : ℍ => PeriodPair.weierstrassP (L τ) (((a₁ : ℂ) * τ + a₂) / N))) ∧

    (∀ L L' : PeriodPair, ∀ c : ℂ, L'.ω₁ = c * L.ω₁ → L'.ω₂ = c * L.ω₂ →
      ∀ z : ℂ, PeriodPair.weierstrassP L' (c * z) =
        c⁻¹ ^ 2 * PeriodPair.weierstrassP L z) := by sorry
