-- Prove2me | Theorems.Thm_TeschlQM_Atomic_atomicHamiltonian_localization_lower_bound_schwartz
-- name    : TeschlQM.Atomic.atomicHamiltonian_localization_lower_bound_schwartz
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-12T07:54:52.262498+00:00
-- url     : https://prove2.me/theorems/671affd4-0dc5-4aa0-a7b0-ebb39d49ff41
-- title:
--   IMS localization lower bound for $H^{(N)}$ on Schwartz functions
-- statement:
--   Let $N\ge1$, $\gamma_{ne},\gamma_{ee}>0$ and $H^{(N-1)}\ge\lambda$. For every $\delta>0$ there is a bounded measurable $W_\delta$ vanishing at infinity such that for every Schwartz function $g$ on $\mathbb R^{3N}$
--   $$\lambda\|g\|^2-\delta\|\nabla g\|^2-\int W_\delta|g|^2\le\|\nabla g\|^2+\int V^{(N)}|g|^2 .$$
--
--   Role: the IMS localization estimate with the Ruelle-Simon partition of unity, stated as a quadratic-form inequality on the Schwartz core: in each region where some electron is far away, $H^{(N)}$ is $H^{(N-1)}$ plus a nonnegative kinetic term plus small interaction errors.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, https://www.mat.univie.ac.at/~gerald/ftp/book-schroe/, Theorem 11.2, proof pp. 243-244 (IMS localization formula with the Ruelle-Simon partition of unity, Lemma 11.3)

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

theorem atomicHamiltonian_localization_lower_bound_schwartz (γne γee : ℝ) (hne : 0 < γne) (hee : 0 < γee)
    (N : ℕ) (hN : 1 ≤ N) (lam : ℝ)
    (hlam : TeschlQM.Shared.IsBoundedBelowBy (atomicHamiltonian γne γee (N - 1)) lam) (δ : ℝ) (hδ : 0 < δ) :
    ∃ W : EuclideanSpace ℝ (Fin N × Fin 3) → ℝ, Measurable W ∧ (∃ C : ℝ, ∀ x, |W x| ≤ C) ∧
      (∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ x, R ≤ ‖x‖ → |W x| ≤ ε) ∧
      ∀ g : SchwartzMap (EuclideanSpace ℝ (Fin N × Fin 3)) ℂ,
        (lam * ∫ x, ‖g x‖ ^ 2)
          - δ * (∑ p : Fin N × Fin 3, ∫ x, ‖fderiv ℝ g x (EuclideanSpace.single p (1 : ℝ))‖ ^ 2)
          - (∫ x, W x * ‖g x‖ ^ 2) ≤
        (∑ p : Fin N × Fin 3, ∫ x, ‖fderiv ℝ g x (EuclideanSpace.single p (1 : ℝ))‖ ^ 2)
          + ∫ x, atomicPotential γne γee N x * ‖g x‖ ^ 2 := by sorry

end TeschlQM.Atomic
