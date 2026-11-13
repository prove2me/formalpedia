-- Prove2me | Theorems.Thm_TeschlQM_Atomic_atomicHamiltonian_exists_min_spectrum
-- name    : TeschlQM.Atomic.atomicHamiltonian_exists_min_spectrum
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-12T10:21:42.483644+00:00
-- url     : https://prove2.me/theorems/e45eb789-241c-4c79-8d0f-7c149fcf0ffa
-- title:
--   The spectrum of the atomic Hamiltonian $H^{(M)}$ has a real minimum
-- statement:
--   Let $H^{(M)}$ be the atomic Hamiltonian (11.6) with $M\ge 0$ electrons and $\gamma_{ne},\gamma_{ee}>0$ (for $M=0$ it is the zero operator on $L^2(\mathbb{R}^0)\cong\mathbb{C}$). Then
--
--   $$\lambda^{M} = \min \sigma(H^{(M)})$$
--
--   exists: $\lambda^M\in\sigma(H^{(M)})$, and every $z\in\sigma(H^{(M)})$ is real with $\lambda^M\le z$.
--
--   Role: defines the ionization threshold $\lambda^{N-1}$ used in the HVZ theorem (Theorem 11.2); it holds because $H^{(M)}$ is self-adjoint (Theorem 11.1) and bounded from below.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, https://www.mat.univie.ac.at/~gerald/ftp/book-schroe/, Theorem 11.1, p. 241, with Theorem 2.18 (spectrum of a self-adjoint operator is a nonempty closed subset of the real line), and the definition of lambda^{N-1} in Theorem 11.2, p. 242

import Mathlib
import Definitions.Def_TeschlQM_Shared_resolventSet
import Definitions.Def_TeschlQM_Shared_essentialSpectrum
import Definitions.Def_TeschlQM_Shared_IsBoundedBelowBy
import Definitions.Def_TeschlQM_Atomic_mulOp
import Definitions.Def_TeschlQM_Atomic_freeHamiltonian
import Definitions.Def_TeschlQM_Atomic_atomicHamiltonian

namespace TeschlQM.Atomic

theorem atomicHamiltonian_exists_min_spectrum (γne γee : ℝ) (hne : 0 < γne) (hee : 0 < γee) (M : ℕ) :
    ∃ lam : ℝ, (lam : ℂ) ∈ TeschlQM.Shared.spectrum (atomicHamiltonian γne γee M) ∧
      ∀ z ∈ TeschlQM.Shared.spectrum (atomicHamiltonian γne γee M), z.im = 0 ∧ lam ≤ z.re := by sorry

end TeschlQM.Atomic
