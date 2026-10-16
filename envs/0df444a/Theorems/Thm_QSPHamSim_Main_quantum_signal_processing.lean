-- Prove2me | Theorems.Thm_QSPHamSim_Main_quantum_signal_processing
-- name    : QSPHamSim.Main.quantum_signal_processing
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T21:26:18.81762+00:00
-- url     : https://prove2.me/theorems/277f1f4b-7e0a-45d6-9702-e292b8f824ef
-- title:
--   Theorem 2 — phases with error 8ε and success at least 1 − 16ε
-- statement:
--   Let $N>0$ be even, let $h:\mathbb R\to(-\pi,\pi]$ be $2\pi$-periodic and odd on $(-\pi,\pi)$, and let $A$ and $C$ be respectively a real cosine series and a real sine series of degree at most $N/2$. Suppose for every real angle $\theta$ that
--   $$
--   |A(\theta)+iC(\theta)-e^{ih(\theta)}|\le\varepsilon.
--   $$
--   There are $N$ real phases, chosen from these data, for which the $|+\rangle$ amplitude of the qubit sequence has squared modulus at least $1-16\varepsilon$ at every $\theta$. For every finite-dimensional input unitary $W=\sum_l e^{i\theta_l}|u_l\rangle\langle u_l|$ and every system vector $\psi$, the same phases satisfy
--   $$
--   \|\bigl(\langle+|V|+\rangle-V_{\mathrm{ideal}}\bigr)\psi\|\le8\varepsilon\|\psi\|,
--   \qquad V_{\mathrm{ideal}}=\sum_l e^{ih(\theta_l)}|u_l\rangle\langle u_l|.
--   $$
--   The theorem converts a finite Fourier approximation into a uniform eigenphase transformation with a success guarantee.
--
--   **Formalization Note** The cosine/sine reading is the form used in Theorem 1. The paper's interval domain is extended periodically to all real angles, while its phase-valued codomain restriction is retained. Oddness is imposed where both an angle and its negative lie in the source's half-open interval, permitting a jump at the identified endpoints. Its efficient computation claim is represented by existence. Success probability is stated pointwise, and the paper's maximum-over-states distance is given as its equivalent homogeneous vector bound. The phases precede the quantifiers over $W$ and $\psi$.
-- source:
--   Low, Chuang, Optimal Hamiltonian Simulation by Quantum Signal Processing, arXiv:1606.02685v2, p. 3, Theorem 2, Eqs. (7)–(8)

import Mathlib
import Definitions.Def_QSPHamSim_Main_Setting

set_option autoImplicit false

namespace QSPHamSim.Main

theorem quantum_signal_processing (N : ℕ) (hN : 0 < N)
    (hNeven : Even N) (h : ℝ → ℝ)
    (hodd : ∀ θ : ℝ, -Real.pi < θ ∧ θ < Real.pi →
      h (-θ) = -h θ)
    (hper : ∀ θ : ℝ, h (θ + 2 * Real.pi) = h θ)
    (hrange : ∀ θ : ℝ, -Real.pi < h θ ∧ h θ ≤ Real.pi)
    (A C : ℝ → ℝ) (hA : IsCosSeries (N / 2) A)
    (hC : IsSinSeries (N / 2) C) (ε : ℝ)
    (happrox : ∀ θ : ℝ,
      ‖((A θ : ℂ) + (C θ : ℂ) * Complex.I) -
        Complex.exp ((h θ : ℂ) * Complex.I)‖ ≤ ε) :
    ∃ φ : Fin N → ℝ,
      (∀ θ : ℝ,
        1 - 16 * ε ≤
          ‖dotProduct (star ketPlus) ((qspSeq N φ θ).mulVec ketPlus)‖ ^ 2) ∧
      ∀ (n : ℕ) (u : Matrix.unitaryGroup (Fin n) ℂ)
        (θs : Fin n → ℝ) (ψ : EuclideanSpace ℂ (Fin n)),
        ‖Matrix.toEuclideanLin
            (plusBlock n (Vop n N u θs φ) - Videal n u θs h) ψ‖ ≤
          8 * ε * ‖ψ‖ := by sorry

end QSPHamSim.Main
