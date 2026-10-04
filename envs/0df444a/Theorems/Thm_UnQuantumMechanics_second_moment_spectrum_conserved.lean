-- Prove2me | Theorems.Thm_UnQuantumMechanics_second_moment_spectrum_conserved
-- name    : UnQuantumMechanics.second_moment_spectrum_conserved
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-02T21:05:54.857986+00:00
-- url     : https://prove2.me/theorems/6abe1387-4069-4259-939b-f9ad7d159386
-- title:
--   Spectral invariants of the second-moment matrix under linear Hamiltonian motion
-- statement:
--   Let $H = \gamma_0 A$ be a Hamiltonian $2n\times 2n$ matrix ($A$ symmetric), the driving matrix of linear Hamiltonian motion $\dot\psi = H\psi$. Let $\tau\mapsto\Sigma(\tau)$ be a matrix of second moments: a real $2n\times 2n$ matrix-valued function, symmetric at every time, that is differentiable and obeys the second-moment equation (40)
--   $$\dot\Sigma = H\Sigma + \Sigma H^T .$$
--   Let $S(\tau) = \Sigma(\tau)\gamma_0^T$ be the autocorrelation matrix. Then for every time $\tau$:
--
--   1. the eigenvalues of $S$ are constants of motion, in the strong form that the characteristic polynomial is conserved:
--   $$\chi_{S(\tau)}(x) = \chi_{S(0)}(x);$$
--   2. all odd powers of $S(\tau)$ are traceless: $\operatorname{Tr}\big(S(\tau)^{2k+1}\big) = 0$ for every $k\in\mathbb N$.
--
--   This is the paper's conclusion (p. 17) that "the result of Hamiltonian evolution in time ... is a symplectic similarity transformation. And since similarity transformations do not change eigenvalues, the eigenvalues are COMs", together with Eq. (48).
--
--   **Formalization Note** Derivatives are entrywise. $\Sigma$ is any symmetric matrix-valued solution of Eq. (40); its interpretation as an ensemble average $\langle\psi\psi^T\rangle$ (and positive semidefiniteness, $\Sigma = KK^T$) is not assumed, because it is not needed. Conservation of the characteristic polynomial (with multiplicities) implies conservation of the whole spectrum and of all $\operatorname{Tr}(S^k)$.
-- source:
--   C. Baumgarten, How to (Un-) Quantum Mechanics, arXiv:1810.06981v2 [physics.gen-ph] (v2 dated June 10, 2025), https://arxiv.org/abs/1810.06981, Sec. V–VI, pp. 15–17: Eqs. (40)–(42), (47), (48), (51) and the sentence after Eq. (51)

import Mathlib
import Definitions.Def_UnQM_phase_space

open Matrix

namespace UnQuantumMechanics

theorem second_moment_spectrum_conserved (n : ℕ) (H : Matrix (PhaseIdx n) (PhaseIdx n) ℝ) (hH : IsHamiltonianMatrix n H)
    (Sig : ℝ → Matrix (PhaseIdx n) (PhaseIdx n) ℝ)
    (hSig : ∀ τ i j, HasDerivAt (fun t => Sig t i j) ((H * Sig τ + Sig τ * Hᵀ) i j) τ)
    (hSym : ∀ t, (Sig t).IsSymm) (τ : ℝ) :
    (autocorr n (Sig τ)).charpoly = (autocorr n (Sig 0)).charpoly ∧
      ∀ k : ℕ, (autocorr n (Sig τ) ^ (2 * k + 1)).trace = 0 := by sorry

end UnQuantumMechanics
