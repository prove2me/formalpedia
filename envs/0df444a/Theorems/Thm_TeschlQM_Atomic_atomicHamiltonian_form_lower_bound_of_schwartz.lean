-- Prove2me | Theorems.Thm_TeschlQM_Atomic_atomicHamiltonian_form_lower_bound_of_schwartz
-- name    : TeschlQM.Atomic.atomicHamiltonian_form_lower_bound_of_schwartz
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-12T07:55:34.218286+00:00
-- url     : https://prove2.me/theorems/ac4ab3be-775e-44b5-a8c6-86be2ee209a4
-- title:
--   A form lower bound for $H^{(N)}$ on Schwartz functions extends to $\mathfrak D(H^{(N)})$
-- statement:
--   Let $W$ be bounded and measurable, and suppose that for every Schwartz function $g$ on $\mathbb R^{3N}$
--   $$\lambda\|g\|^2-\delta\|\nabla g\|^2-\int W|g|^2\le\|\nabla g\|^2+\int V^{(N)}|g|^2 .$$
--   Then for every $\psi\in\mathfrak D(H^{(N)})=\mathfrak D(H_0)\cap\mathfrak D(V^{(N)})$
--   $$\lambda\|\psi\|^2-\delta\langle\psi,H_0\psi\rangle-\int W|\psi|^2\le\langle\psi,H^{(N)}\psi\rangle .$$
--
--   Role: Schwartz functions are a core for $H_0$ and $V^{(N)}$ is $H_0$-bounded (Hardy's inequality), so quadratic-form inequalities proved on the Schwartz core extend to the operator domain of $H^{(N)}$.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, https://www.mat.univie.ac.at/~gerald/ftp/book-schroe/, Theorem 11.1 and its proof p. 242 (V^{(N)} is H_0-bounded via Hardy's inequality), Section 7.1 (the Schwartz space is a core for H_0 = -Delta)

import Mathlib
import Definitions.Def_TeschlQM_Shared_resolventSet
import Definitions.Def_TeschlQM_Shared_essentialSpectrum
import Definitions.Def_TeschlQM_Shared_IsBoundedBelowBy
import Definitions.Def_TeschlQM_Shared_IsSymmetric
import Definitions.Def_TeschlQM_Atomic_mulOp
import Definitions.Def_TeschlQM_Atomic_freeHamiltonian
import Definitions.Def_TeschlQM_Atomic_atomicHamiltonian
open MeasureTheory Filter

namespace TeschlQM.Atomic

theorem atomicHamiltonian_form_lower_bound_of_schwartz (γne γee : ℝ) (N : ℕ) (lam δ : ℝ)
    (W : EuclideanSpace ℝ (Fin N × Fin 3) → ℝ) (hWm : Measurable W) (C : ℝ) (hWC : ∀ x, |W x| ≤ C)
    (hS : ∀ g : SchwartzMap (EuclideanSpace ℝ (Fin N × Fin 3)) ℂ,
        (lam * ∫ x, ‖g x‖ ^ 2)
          - δ * (∑ p : Fin N × Fin 3, ∫ x, ‖fderiv ℝ g x (EuclideanSpace.single p (1 : ℝ))‖ ^ 2)
          - (∫ x, W x * ‖g x‖ ^ 2) ≤
        (∑ p : Fin N × Fin 3, ∫ x, ‖fderiv ℝ g x (EuclideanSpace.single p (1 : ℝ))‖ ^ 2)
          + ∫ x, atomicPotential γne γee N x * ‖g x‖ ^ 2)
    (ψ : (freeHamiltonian (Fin N × Fin 3)).domain)
    (hψ : (ψ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin N × Fin 3)))) ∈ (atomicHamiltonian γne γee N).domain) :
    lam * ‖(ψ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin N × Fin 3))))‖ ^ 2
      - δ * (inner ℂ (ψ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin N × Fin 3)))) (freeHamiltonian (Fin N × Fin 3) ψ)).re
      - ∫ x, W x * ‖((ψ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin N × Fin 3)))) : EuclideanSpace ℝ (Fin N × Fin 3) → ℂ) x‖ ^ 2
      ≤ (inner ℂ (ψ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin N × Fin 3)))) (atomicHamiltonian γne γee N ⟨ψ, hψ⟩)).re := by sorry

end TeschlQM.Atomic
