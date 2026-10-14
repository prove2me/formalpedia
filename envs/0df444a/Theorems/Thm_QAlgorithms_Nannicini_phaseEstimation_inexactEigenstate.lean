-- Prove2me | Theorems.Thm_QAlgorithms_Nannicini_phaseEstimation_inexactEigenstate
-- name    : QAlgorithms.Nannicini.phaseEstimation_inexactEigenstate
-- status  : Open
-- author  : @Goku
-- created : 2026-10-13T17:45:21.353151+00:00
-- url     : https://prove2.me/theorems/639dd6e2-d5dd-40c9-a1a6-ab35ecafd794
-- title:
--   Phase estimation on an inexact eigenstate succeeds with probability at least (1 − δ)|⟨ξ|ψ*⟩|²
-- statement:
--   Let $U$ be a unitary on $n$ qubits and fix the number $m$ of estimation qubits of the phase estimation circuit (Fig. 3.6): $H^{\otimes m}$ on $|0\rangle_m$, the controlled powers $U^{2^j}$, the inverse QFT $Q_m^\dagger$, and a measurement of the first register, whose outcome $p\in\{0,1\}^m$ is read as the phase estimate $0.p = p/2^m$. Distances between phases are measured on the circle, $d(x,y)=\min\{|x-y|,1-|x-y|\}$ for $x,y\in[0,1)$.
--
--   Assume the circuit performs phase estimation with precision $\epsilon>0$ and probability of success at least $1-\delta$, $\delta\in[0,1]$: for every unit eigenvector $v$ of $U$ with eigenvalue $e^{2\pi i\varphi}$, $\varphi\in[0,1)$, the outcome $p$ satisfies $d(0.p,\varphi)<\epsilon$ with probability at least $1-\delta$. Let $|\psi^*\rangle$ be a unit eigenvector of $U$ with eigenvalue $e^{2\pi i\varphi^*}$, $\varphi^*\in[0,1)$, and let $|\xi\rangle$ be any quantum state. Then running the circuit on $|0\rangle_m\otimes|\xi\rangle$ gives an outcome $p^*$ with
--
--   $$
--   \Pr\big[d(0.p^*,\varphi^*)<\epsilon\big]\ \ge\ (1-\delta)\,|\langle\xi|\psi^*\rangle|^2 .
--   $$
--
--   The result quantifies how the success probability of phase estimation degrades when only an approximate eigenstate can be prepared: it is the guaranteed success probability scaled by the overlap with the target eigenstate.
--
--   **Formalization Note** The output state of the circuit is the shared definition `phaseEstimationState m U ξ`; the assumption on the procedure is a hypothesis quantified over all unit eigenvectors, as in Thm. 3.9.
-- source:
--   Giacomo Nannicini, Quantum algorithms for optimizers, 2025, v5; notes dated 9 July 2025, PDF p. 63, Proposition 3.14. https://arxiv.org/pdf/2408.07086v5

import Definitions.Def_QAlgorithms_Defs_AmplitudeEstimation
set_option autoImplicit false

namespace QAlgorithms.Nannicini

open QAlgorithms

/-- Nannicini p.63, Proposition 3.14 (phase estimation on an inexact eigenstate): suppose
phase estimation with `m` estimation qubits (Fig. 3.6) has precision `ε` and probability of
success `≥ 1 − δ`, i.e. on every unit eigenvector `v` of `U` with eigenvalue `e^{2πiφ}`,
`φ ∈ [0, 1)`, the output `p` satisfies `circDist (0.p) φ < ε` with probability `≥ 1 − δ`
(the guarantee of Thm. 3.9, p.62). Let `ψ*` be a unit eigenvector with eigenvalue `e^{2πiφ*}`
and `ξ` any state. Then running the circuit on `ξ` outputs `p*` with `circDist (0.p*) φ* < ε`
with probability at least `(1 − δ) |⟨ξ|ψ*⟩|²`. -/
theorem phaseEstimation_inexactEigenstate (n m : ℕ) (U : Matrix (Qubits n) (Qubits n) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Qubits n) ℂ) (ε δ : ℝ) (hε : 0 < ε) (hδ0 : 0 ≤ δ)
    (hδ1 : δ ≤ 1)
    (hQPE : ∀ (v : EuclideanSpace ℂ (Qubits n)) (φ : ℝ), IsState v → 0 ≤ φ → φ < 1 →
      act U v = Complex.exp (2 * Real.pi * Complex.I * (φ : ℂ)) • v →
      probEvent (phaseEstimationState m U v)
        (fun z => circDist ((bitsToNat z.1 : ℝ) / (2 : ℝ) ^ m) φ < ε) ≥ 1 - δ)
    (psiStar : EuclideanSpace ℂ (Qubits n)) (phiStar : ℝ) (hpsi : IsState psiStar)
    (hphi0 : 0 ≤ phiStar) (hphi1 : phiStar < 1)
    (heig : act U psiStar = Complex.exp (2 * Real.pi * Complex.I * (phiStar : ℂ)) • psiStar)
    (xi : EuclideanSpace ℂ (Qubits n)) (hxi : IsState xi) :
    probEvent (phaseEstimationState m U xi)
        (fun z => circDist ((bitsToNat z.1 : ℝ) / (2 : ℝ) ^ m) phiStar < ε) ≥
      (1 - δ) * ‖inner ℂ xi psiStar‖ ^ 2 := by sorry



end QAlgorithms.Nannicini
