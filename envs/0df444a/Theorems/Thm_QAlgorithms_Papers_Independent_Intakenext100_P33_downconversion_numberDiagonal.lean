-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P33_downconversion_numberDiagonal
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P33.downconversion_numberDiagonal
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:09:49.257552+00:00
-- url     : https://prove2.me/theorems/091ed8dc-14ab-4f92-8e56-31e01912c907
-- title:
--   Exact downconversion preserves weighted photon number and yields a diagonal signal
-- statement:
--   Consider two full oscillator modes, pump $a$ and signal $b$, with real coupling $\chi$ and interaction Hamiltonian
--
--   $$
--   H_I=\chi\bigl(a^\dagger b^2+(b^\dagger)^2a\bigr),\qquad W=2N_a+N_b.
--   $$
--
--   The Hamiltonian is constructed on the finite-occupation core with the usual square-root ladder coefficients and guarded lowering boundaries. It satisfies $H_IW=WH_I$ there. Every fixed-$W$ sector has a finite Hermitian matrix, and for every real time $t$ its matrix exponential $e^{-itH_I}$ is unitary. Their explicitly constructed direct sum realizes a unitary on the full two-mode Hilbert space and preserves each weighted-number sector; square summability of its computed coefficients is a conclusion.
--
--   Let $p_m\ge0$, $\sum_mp_m=1$, with the series summable, be any pump photon-number distribution. The initial state is $\sum_mp_m|m\rangle\langle m|\otimes|0\rangle\langle0|$. Write $\psi_m(t)=U(t)|m,0\rangle$. The computed reduced signal has the bounded occupation matrix
--
--   $$
--   \langle n|\rho_b(t)|l\rangle=\sum_{m,j\ge0}p_m\,\psi_m(t)_{j,n}\overline{\psi_m(t)_{j,l}}.
--   $$
--
--   These sums converge, the resulting operator is positive trace class of trace one, and every off-diagonal entry vanishes. Its diagonal probability is $\sum_{m,j}p_m|\psi_m(t)_{j,n}|^2$, with convergence asserted.
--
--   No finite-energy or finite-support assumption is imposed on the pump law, and no undepleted-pump approximation is used. Vacuum input or zero coupling gives vacuum signal.
-- source:
--   The Quantum State of a Propagating Laser Field, arXiv:quant-ph/0111157v1, PDF p. 7, IIIC, Eq.(32) and following paragraph

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P33

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P33

open Filter MeasureTheory

open scoped Topology Matrix ComplexConjugate

attribute [local instance] Classical.propDecidable

open QAlgorithms.Papers.Independent.Dependency50.P39

-- Accepted scalar phase; positive exponential, differing only by commuting scalars.

open QAlgorithms.Papers.Independent.Information100.P75 (phase)

/-- arXiv:quant-ph/0111157v1, PDF p.7, Eq.(32) and following paragraph.
The cubic Hamiltonian conserves 2Na+Nb on its core, and the constructed
finite-block direct sum is unitary and preserves weighted-number sectors.
Every normalized number-diagonal pump law, with signal vacuum, gives a
normalized trace-class number-diagonal signal. No finite moment or undepleted
pump approximation is imposed, and no commutation or output identity is assumed. -/
theorem downconversion_numberDiagonal (chi t : ℝ) :
    (∀ v : DownCore, downHamiltonian chi (weightedNumber v) =
      weightedNumber (downHamiltonian chi v)) ∧
    (∀ w, (downBlock chi w).IsHermitian ∧
      downBlockEvolution chi t w ∈ Matrix.unitaryGroup (Fin (w / 2 + 1)) ℂ) ∧
    (∀ v : BipartiteFock, Memℓp (downCoefficients chi t v) 2 ∧
      ∀ q, downEvolution chi t v q = downCoefficients chi t v q) ∧
    (∃ U : BipartiteFock ≃ₗᵢ[ℂ] BipartiteFock,
      ∀ v, U v = downEvolution chi t v) ∧
    (∀ (w : ℕ) (v : BipartiteFock),
      (∀ q, 2 * q.1 + q.2 ≠ w → v q = 0) →
      ∀ q, 2 * q.1 + q.2 ≠ w → downEvolution chi t v q = 0) ∧
    (∀ p : ℕ → ℝ, (∀ m, 0 ≤ p m) → Summable p → (∑' m, p m) = 1 →
      (∀ n l, Summable (fun k : ℕ × ℕ =>
        (p k.1 : ℂ) * evolvedPumpNumber chi t k.1 (k.2, n) *
          star (evolvedPumpNumber chi t k.1 (k.2, l)))) ∧
      HasFockMatrix (signalOutput p chi t) (signalMatrix p chi t) ∧
      IsDensity (signalOutput p chi t) ∧
      (∀ n l, n ≠ l → signalOutput p chi t (fockKet l) n = 0) ∧
      (∀ n, (signalOutput p chi t (fockKet n) n).re =
        ∑' k : ℕ × ℕ, p k.1 * Complex.normSq (evolvedPumpNumber chi t k.1 (k.2, n))) ∧
      (∀ n, Summable (fun k : ℕ × ℕ =>
        p k.1 * Complex.normSq (evolvedPumpNumber chi t k.1 (k.2, n))))) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P33

end
