-- Prove2me | Theorems.Thm_TeschlQM_Atomic_atomicHamiltonian_isBoundedBelow
-- name    : TeschlQM.Atomic.atomicHamiltonian_isBoundedBelow
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-12T10:21:07.130472+00:00
-- url     : https://prove2.me/theorems/dda9ca01-206a-463e-86c8-24aa261b709d
-- title:
--   The atomic Hamiltonian $H^{(N)}$ is bounded from below
-- statement:
--   Let $H^{(N)} = H_0 + V^{(N)}$ be the atomic Hamiltonian (11.6) in $L^2(\mathbb{R}^{3N})$ with $\gamma_{ne},\gamma_{ee}>0$ (11.7). Then there is $\gamma\in\mathbb{R}$ with
--
--   $$\langle \psi, H^{(N)}\psi\rangle \ge \gamma\,\|\psi\|^2 \qquad (\psi\in\mathfrak{D}(H^{(N)})).$$
--
--   Role: the first assertion of the HVZ theorem (Theorem 11.2): $H^{(N)}$ is bounded from below.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, https://www.mat.univie.ac.at/~gerald/ftp/book-schroe/, Theorem 11.1 and the discussion of (11.6)-(11.7), p. 241

import Mathlib
import Definitions.Def_TeschlQM_Shared_resolventSet
import Definitions.Def_TeschlQM_Shared_essentialSpectrum
import Definitions.Def_TeschlQM_Shared_IsBoundedBelowBy
import Definitions.Def_TeschlQM_Atomic_mulOp
import Definitions.Def_TeschlQM_Atomic_freeHamiltonian
import Definitions.Def_TeschlQM_Atomic_atomicHamiltonian

namespace TeschlQM.Atomic

theorem atomicHamiltonian_isBoundedBelow (γne γee : ℝ) (hne : 0 < γne) (hee : 0 < γee) (N : ℕ) :
    ∃ γ : ℝ, TeschlQM.Shared.IsBoundedBelowBy (atomicHamiltonian γne γee N) γ := by sorry

end TeschlQM.Atomic
