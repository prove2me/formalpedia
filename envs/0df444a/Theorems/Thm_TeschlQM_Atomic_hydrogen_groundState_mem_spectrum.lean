-- Prove2me | Theorems.Thm_TeschlQM_Atomic_hydrogen_groundState_mem_spectrum
-- name    : TeschlQM.Atomic.hydrogen_groundState_mem_spectrum
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-12T10:22:16.712696+00:00
-- url     : https://prove2.me/theorems/adc1e71f-f03a-44e4-aa59-38ed0ab79d9e
-- title:
--   The hydrogen ground-state energy $-\gamma_{ne}^2/4$ lies in $\sigma(H^{(1)})$
-- statement:
--   Let $H^{(1)} = -\Delta - \gamma_{ne}/|x|$ be the one-electron atomic Hamiltonian (11.6) in $L^2(\mathbb{R}^3)$, $\gamma_{ne}>0$ (the hydrogen atom). Then
--
--   $$-\frac{\gamma_{ne}^2}{4} \in \sigma(H^{(1)}),$$
--
--   the ground-state energy, with eigenfunction $\psi(x)=e^{-\gamma_{ne}|x|/2}$.
--
--   Role: the base case $\lambda^1<0$ of the negativity claim $\lambda^{N-1}<0$ ($N\ge2$) in the HVZ theorem (Theorem 11.2).
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, https://www.mat.univie.ac.at/~gerald/ftp/book-schroe/, Section 10.4 (The hydrogen atom), eigenvalues -gamma^2/(4n^2) with n = 1

import Mathlib
import Definitions.Def_TeschlQM_Shared_resolventSet
import Definitions.Def_TeschlQM_Shared_essentialSpectrum
import Definitions.Def_TeschlQM_Shared_IsBoundedBelowBy
import Definitions.Def_TeschlQM_Atomic_mulOp
import Definitions.Def_TeschlQM_Atomic_freeHamiltonian
import Definitions.Def_TeschlQM_Atomic_atomicHamiltonian

namespace TeschlQM.Atomic

theorem hydrogen_groundState_mem_spectrum (γne γee : ℝ) (hne : 0 < γne) (hee : 0 < γee) :
    (((-(γne ^ 2 / 4) : ℝ)) : ℂ) ∈ TeschlQM.Shared.spectrum (atomicHamiltonian γne γee 1) := by sorry

end TeschlQM.Atomic
