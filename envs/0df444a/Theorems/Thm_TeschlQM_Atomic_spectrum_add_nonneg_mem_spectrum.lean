-- Prove2me | Theorems.Thm_TeschlQM_Atomic_spectrum_add_nonneg_mem_spectrum
-- name    : TeschlQM.Atomic.spectrum_add_nonneg_mem_spectrum
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-12T09:09:33.681502+00:00
-- url     : https://prove2.me/theorems/e7a963b7-a79d-4ad2-9b5b-3840489cf4ea
-- title:
--   $\sigma(H^{(N-1)})+[0,\infty)\subseteq\sigma(H^{(N)})$
-- statement:
--   Let $N\ge1$, $\gamma_{ne},\gamma_{ee}>0$, and suppose $H^{(N-1)}$ is symmetric with a real point $t$ in its resolvent set (so it is self-adjoint; Theorem 11.1). If $\mu\in\mathbb R$ lies in $\sigma(H^{(N-1)})$ and $s\ge0$, then
--   $$\mu+s\in\sigma(H^{(N)}).$$
--
--   Role: the inclusion $[\lambda^{N-1},\infty)\subseteq\sigma(H^{(N)})$ in (11.9): a Weyl sequence for $H^{(N-1)}$ at $\mu$ tensored with a plane wave of energy $s$ for the $N$-th electron, translated to infinity.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, https://www.mat.univie.ac.at/~gerald/ftp/book-schroe/, Theorem 11.2, proof p. 243 (first part: sigma(H^{N-1}) + [0,infty) subset sigma(H^N) via Weyl sequences)

import Mathlib
import Definitions.Def_TeschlQM_Shared_resolventSet
import Definitions.Def_TeschlQM_Shared_essentialSpectrum
import Definitions.Def_TeschlQM_Shared_IsBoundedBelowBy
import Definitions.Def_TeschlQM_Shared_IsSymmetric
import Definitions.Def_TeschlQM_Atomic_mulOp
import Definitions.Def_TeschlQM_Atomic_freeHamiltonian
import Definitions.Def_TeschlQM_Atomic_atomicHamiltonian

namespace TeschlQM.Atomic

theorem spectrum_add_nonneg_mem_spectrum (γne γee : ℝ) (hne : 0 < γne) (hee : 0 < γee) (N : ℕ)
    (hN : 1 ≤ N)
    (hsym : TeschlQM.Shared.IsSymmetric (atomicHamiltonian γne γee (N - 1)))
    (hres : ∃ t : ℝ, (t : ℂ) ∈ TeschlQM.Shared.resolventSet (atomicHamiltonian γne γee (N - 1)))
    (μ : ℝ) (hμ : (μ : ℂ) ∈ TeschlQM.Shared.spectrum (atomicHamiltonian γne γee (N - 1)))
    (s : ℝ) (hs : 0 ≤ s) :
    ((μ + s : ℝ) : ℂ) ∈ TeschlQM.Shared.spectrum (atomicHamiltonian γne γee N) := by sorry

end TeschlQM.Atomic
