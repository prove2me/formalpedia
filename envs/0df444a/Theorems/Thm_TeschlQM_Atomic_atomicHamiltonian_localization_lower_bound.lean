-- Prove2me | Theorems.Thm_TeschlQM_Atomic_atomicHamiltonian_localization_lower_bound
-- name    : TeschlQM.Atomic.atomicHamiltonian_localization_lower_bound
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-12T07:33:36.8335+00:00
-- url     : https://prove2.me/theorems/ae03a8e6-f400-4e45-a737-120cafa683d7
-- title:
--   IMS localization lower bound $H^{(N)}\ge\lambda^{N-1}-\delta-\delta H_0-W_\delta$
-- statement:
--   Let $N\ge1$, $\gamma_{ne},\gamma_{ee}>0$ and $H^{(N-1)}\ge\lambda$. For every $\delta>0$ there is a bounded measurable $W_\delta$ vanishing at infinity with
--   $$\langle\psi,H^{(N)}\psi\rangle\ge(\lambda-\delta)\|\psi\|^2-\delta\langle\psi,H_0\psi\rangle-\int W_\delta|\psi|^2$$
--   for all $\psi\in D(H^{(N)})$.
--
--   Role: the IMS localization estimate with the Ruelle–Simon partition of unity: in each region where some electron is far away, $H^{(N)}$ is $H^{(N-1)}$ plus a nonnegative kinetic term plus small interaction errors.
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

theorem atomicHamiltonian_localization_lower_bound (γne γee : ℝ) (hne : 0 < γne) (hee : 0 < γee)
    (N : ℕ) (hN : 1 ≤ N) (lam : ℝ)
    (hlam : TeschlQM.Shared.IsBoundedBelowBy (atomicHamiltonian γne γee (N - 1)) lam) (δ : ℝ) (hδ : 0 < δ) :
    ∃ W : EuclideanSpace ℝ (Fin N × Fin 3) → ℝ, Measurable W ∧ (∃ C : ℝ, ∀ x, |W x| ≤ C) ∧
      (∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ x, R ≤ ‖x‖ → |W x| ≤ ε) ∧
      ∀ (ψ : (freeHamiltonian (Fin N × Fin 3)).domain)
        (hψ : (ψ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin N × Fin 3)))) ∈ (atomicHamiltonian γne γee N).domain),
        (lam - δ) * ‖(ψ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin N × Fin 3))))‖ ^ 2
          - δ * (inner ℂ (ψ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin N × Fin 3)))) (freeHamiltonian (Fin N × Fin 3) ψ)).re
          - ∫ x, W x * ‖((ψ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin N × Fin 3)))) : EuclideanSpace ℝ (Fin N × Fin 3) → ℂ) x‖ ^ 2
          ≤ (inner ℂ (ψ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin N × Fin 3)))) (atomicHamiltonian γne γee N ⟨ψ, hψ⟩)).re := by sorry

end TeschlQM.Atomic
