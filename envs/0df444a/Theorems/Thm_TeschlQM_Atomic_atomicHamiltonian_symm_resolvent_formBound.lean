-- Prove2me | Theorems.Thm_TeschlQM_Atomic_atomicHamiltonian_symm_resolvent_formBound
-- name    : TeschlQM.Atomic.atomicHamiltonian_symm_resolvent_formBound
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-12T09:08:49.873933+00:00
-- url     : https://prove2.me/theorems/1527f5c1-460f-4f60-b123-0b47c1be99e7
-- title:
--   $H^{(N)}$ is symmetric, has a real resolvent point, is bounded below and controls the kinetic form
-- statement:
--   Let $H^{(N)}=H_0+V$ be the atomic Hamiltonian (11.6) with $\gamma_{ne},\gamma_{ee}>0$. Then $H^{(N)}$ is symmetric, some real $t$ lies in its resolvent set, $H^{(N)}\ge\gamma$ for some $\gamma\in\mathbb R$, and there is $C$ with
--   $$\langle\psi,H_0\psi\rangle\le 2\langle\psi,H^{(N)}\psi\rangle+C\|\psi\|^2\qquad(\psi\in D(H^{(N)})).$$
--
--   Role: the self-adjointness and semiboundedness input (Theorem 11.1, via Kato–Rellich and Hardy's inequality) that the essential-spectrum identity needs: Weyl sequences are $H_0$-form bounded.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, https://www.mat.univie.ac.at/~gerald/ftp/book-schroe/, Theorem 11.1 (p. 241, self-adjointness and semiboundedness of H^(N) via Kato-Rellich and the Hardy relative bound); used in the proof of Theorem 11.2, p. 243

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

theorem atomicHamiltonian_symm_resolvent_formBound (γne γee : ℝ) (hne : 0 < γne) (hee : 0 < γee) (N : ℕ) :
    TeschlQM.Shared.IsSymmetric (atomicHamiltonian γne γee N) ∧
    (∃ t : ℝ, (t : ℂ) ∈ TeschlQM.Shared.resolventSet (atomicHamiltonian γne γee N)) ∧
    (∃ γ : ℝ, TeschlQM.Shared.IsBoundedBelowBy (atomicHamiltonian γne γee N) γ) ∧
    ∃ C : ℝ, ∀ (ψ : (freeHamiltonian (Fin N × Fin 3)).domain)
      (hψ : (ψ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin N × Fin 3)))) ∈ (atomicHamiltonian γne γee N).domain),
      (inner ℂ (ψ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin N × Fin 3)))) (freeHamiltonian (Fin N × Fin 3) ψ)).re ≤
        2 * (inner ℂ (ψ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin N × Fin 3)))) (atomicHamiltonian γne γee N ⟨ψ, hψ⟩)).re +
        C * ‖(ψ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin N × Fin 3))))‖ ^ 2 := by sorry

end TeschlQM.Atomic
