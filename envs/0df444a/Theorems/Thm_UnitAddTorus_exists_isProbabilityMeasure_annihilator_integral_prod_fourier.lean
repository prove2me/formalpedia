-- Prove2me | Theorems.Thm_UnitAddTorus_exists_isProbabilityMeasure_annihilator_integral_prod_fourier
-- name    : UnitAddTorus.exists_isProbabilityMeasure_annihilator_integral_prod_fourier
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.683932+00:00
-- url     : https://prove2.me/theorems/58a685d1-761e-5d5f-8b7d-1de4ee1d56a9
-- title:
--   Haar probability measure on the annihilator of Q⊆ℤᵈ
-- statement:
--   Let $d$ be a natural number and let $Q$ be an additive subgroup of $\mathbb{Z}^d$, written as $\mathrm{Fin}\,d\to\mathbb{Z}$. Write $\mathbb{T}^d$ for $\mathrm{Fin}\,d\to\mathbb{R}/\mathbb{Z}$, where the circle is `AddCircle (1 : ℝ)`, and for $n\in\mathbb{Z}^d$ let $e_n(\theta)=\prod_{i}\mathrm{fourier}(n_i)(\theta_i)$ be the associated $\mathbb{C}$-valued character, built from Mathlib's Fourier characters of period $1$. Put $Q^{\perp}=\{\theta\in\mathbb{T}^d:\ e_q(\theta)=1\ \text{for all}\ q\in Q\}$. The assertion is that there exists a measure $m$ on $\mathbb{T}^d$ with the following four properties: $m$ is a probability measure; the complement of $Q^{\perp}$ is $m$-null, $m\big((Q^{\perp})^{c}\big)=0$; for every $n\in\mathbb{Z}^d$ lying in $Q$ one has $\int_{\mathbb{T}^d}e_n\,dm=1$, and for every $n\in\mathbb{Z}^d$ not lying in $Q$ one has $\int_{\mathbb{T}^d}e_n\,dm=0$; and, under the additional hypothesis that the set $Q^{\perp}$ is infinite, $m(\{\theta\})=0$ for every single point $\theta\in\mathbb{T}^d$. The integrals are Bochner integrals of complex-valued functions with respect to $m$.
--
--   This is the standard harmonic-analytic input on the compact abelian group $\mathbb{T}^d$: the normalised Haar measure of the closed annihilator subgroup $Q^{\perp}$, viewed as a measure on $\mathbb{T}^d$, together with the orthogonality relations for characters (equivalently the duality $Q^{\perp\perp}=Q$) and the fact that the Haar measure of an infinite compact group has no atoms. It is used in the construction of a measure-theoretic limit interpolating values of characters on a discrete subgroup, in the step recorded as [`MeasureTheory.exists_forall_exists_clm_opNorm_le_noAtomicMass_forall_hasSum_fibre_mul_fourier_eq_apply_fourier_of_le_of_discrete_of_productFormula_of_fourier_decay`](thm.html#MeasureTheory.exists_forall_exists_clm_opNorm_le_noAtomicMass_forall_hasSum_fibre_mul_fourier_eq_apply_fourier_of_le_of_discrete_of_productFormula_of_fourier_decay).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_UnitAddTorus_exists_isProbabilityMeasure_annihilator_integral_prod_fourier.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory

theorem UnitAddTorus.exists_isProbabilityMeasure_annihilator_integral_prod_fourier
    (d : ℕ) (Q : AddSubgroup (Fin d → ℤ)) :
    ∃ m : Measure (Fin d → AddCircle (1 : ℝ)), IsProbabilityMeasure m ∧
      m {θ : Fin d → AddCircle (1 : ℝ) | ∀ q ∈ Q, (∏ i, fourier (q i) (θ i)) = 1}ᶜ = 0 ∧
      (∀ n : Fin d → ℤ, n ∈ Q → ∫ θ, (∏ i, fourier (n i) (θ i)) ∂m = 1) ∧
      (∀ n : Fin d → ℤ, n ∉ Q → ∫ θ, (∏ i, fourier (n i) (θ i)) ∂m = 0) ∧
      ({θ : Fin d → AddCircle (1 : ℝ) | ∀ q ∈ Q, (∏ i, fourier (q i) (θ i)) = 1}.Infinite →
        ∀ θ : Fin d → AddCircle (1 : ℝ), m {θ} = 0) := by sorry
