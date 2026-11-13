-- Prove2me | Theorems.Thm_TeschlQM_Atomic_essentialSpectrum_atomicHamiltonian_eq_Ici
-- name    : TeschlQM.Atomic.essentialSpectrum_atomicHamiltonian_eq_Ici
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-12T06:35:08.518195+00:00
-- url     : https://prove2.me/theorems/d6263724-d9fb-4e6e-a342-45fa4b8e302a
-- title:
--   $\sigma_{ess}(H^{(N)}) = [\lambda^{N-1},\infty)$ for the atomic Hamiltonian
-- statement:
--   Let $H^{(N)}$ be the atomic Hamiltonian (11.6) with $N\ge 1$ electrons and $\gamma_{ne},\gamma_{ee}>0$, and let $\lambda=\min\sigma(H^{(N-1)})$, i.e. $\lambda\in\sigma(H^{(N-1)})$ and every $z\in\sigma(H^{(N-1)})$ is real with $\lambda\le z$. Then
--
--   $$\sigma_{ess}(H^{(N)}) = [\lambda,\infty).$$
--
--   Role: the essential-spectrum identity (11.9), the core of the HVZ theorem (Theorem 11.2).
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, https://www.mat.univie.ac.at/~gerald/ftp/book-schroe/, Theorem 11.2, equation (11.9), proof pp. 242-244

import Mathlib
import Definitions.Def_TeschlQM_Shared_resolventSet
import Definitions.Def_TeschlQM_Shared_essentialSpectrum
import Definitions.Def_TeschlQM_Shared_IsBoundedBelowBy
import Definitions.Def_TeschlQM_Atomic_mulOp
import Definitions.Def_TeschlQM_Atomic_freeHamiltonian
import Definitions.Def_TeschlQM_Atomic_atomicHamiltonian

namespace TeschlQM.Atomic

theorem essentialSpectrum_atomicHamiltonian_eq_Ici (γne γee : ℝ) (hne : 0 < γne) (hee : 0 < γee) (N : ℕ)
    (hN : 1 ≤ N) (lam : ℝ)
    (hlam : (lam : ℂ) ∈ TeschlQM.Shared.spectrum (atomicHamiltonian γne γee (N - 1)))
    (hmin : ∀ z ∈ TeschlQM.Shared.spectrum (atomicHamiltonian γne γee (N - 1)), z.im = 0 ∧ lam ≤ z.re) :
    TeschlQM.Shared.essentialSpectrum (atomicHamiltonian γne γee N) =
      (fun t : ℝ => (t : ℂ)) '' Set.Ici lam := by sorry

end TeschlQM.Atomic
