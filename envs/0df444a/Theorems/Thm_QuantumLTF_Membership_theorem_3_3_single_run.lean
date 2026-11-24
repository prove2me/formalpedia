-- Prove2me | Theorems.Thm_QuantumLTF_Membership_theorem_3_3_single_run
-- name    : QuantumLTF.Membership.theorem_3_3_single_run
-- status  : Proved
-- author  : @Mr Robbins
-- created : 2026-11-23T02:28:44.548848+00:00
-- url     : https://prove2.me/theorems/eb281848-f164-45bd-b104-64e69f51b77b
-- title:
--   One approximate Jordan run for the scaled height gradient
-- statement:
--   This is the single-run estimate in the proof of Theorem 3.3, before median amplification.
--
--   Let $n\ge2$, $0<\epsilon\le1/2$, and $0<\epsilon_g\le10$. Put
--   $$\eta=\frac{\rho\epsilon_g}{48\pi(3n+1)},\qquad b=\left\lceil\log_2\frac{3n+1}{\rho\epsilon_g}\right\rceil,$$
--   where $\rho=2^{-\lceil\log_2(40\sqrt n)\rceil}$. For a value-register format obeying the same width bound as in Theorem 3.3, there is an oracle circuit, chosen independently of $w,\theta,p$ and of the height oracle, with the following properties. It uses $O(1)$ calls to the height oracle or its inverse and
--   $$O\!\left(n\log^2(n/\epsilon_g)+\log(1/\epsilon)\right)$$
--   other one- and two-qubit gates. If $|H̃_p(x)-h_p(\rho x)|\le\eta$ on the centered grid and $1/10\le|\langle w,p\rangle|\le3$ with $\|w\|=1$, then with probability at least $3/4$ its fixed-point output $\widetilde g$ satisfies
--   $$\max_i|\widetilde g_i-(-w_i/\langle w,p\rangle)|\le\epsilon_g.$$
--   The last display-width inequality is circuit accounting needed when this run is replicated: the total number $n\ell_o$ of output wires has the same asymptotic bound, with an additive $O(1)$.
--
--   Mathematically, this packages Eqs. (52)–(58): exact affine phase factorization, the simultaneous phase-estimation union bound, and approximation of the phase state to trace distance at most $1/12$.
-- source:
--   Krivcenko–Nguyen–de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, arXiv:2609.40331, proof of Theorem 3.3, pp. 28–30 (PDF pp. 29–31), especially Eqs. (52)–(58) and the success probability 5/6−1/12=3/4.

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QAlgorithms_Defs_GradientMethods
import Definitions.Def_QuantumLTF_Membership_fpVal
import Definitions.Def_QuantumLTF_Membership_readFp
import Definitions.Def_QuantumLTF_Membership_gates12
import Definitions.Def_QuantumLTF_Membership_Uncontrolled
import Definitions.Def_QuantumLTF_Membership_height
import Definitions.Def_QuantumLTF_Membership_rho
import Definitions.Def_QuantumLTF_Membership_gridVec
import Definitions.Def_QuantumLTF_Membership_regBasis

open QAlgorithms

/-- The single-run part of the proof of Theorem 3.3, pp. 28–30 (PDF pp. 29–31), Eqs. (52)–(58):
one approximate affine phase application and centered-grid Fourier readout give every gradient coordinate
to error `εg`, simultaneously with probability at least `3/4`, using constantly many height-oracle calls. -/
theorem QuantumLTF.Membership.theorem_3_3_single_run (C₁ : ℝ) (hC₁ : 0 ≤ C₁) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n → ∀ ε εg : ℝ, 0 < ε → ε ≤ 1 / 2 →
      0 < εg → εg ≤ 10 →
      let η : ℝ := rho n * εg / (48 * Real.pi * (3 * n + 1))
      let b : ℕ := ⌈Real.logb 2 ((3 * n + 1) / (rho n * εg))⌉₊
      ∀ Vb Vf W : ℕ, (Vb : ℝ) ≤ C₁ * (Real.log (1 / ε) + Real.log (1 / η)) →
        ∃ (m ℓo fo : ℕ) (c : OracleCircuit gates12 (fun _ : Fin 1 => n * b + Vb + W) m)
          (oa : Fin n → (Fin ℓo ↪ Fin m)),
          Uncontrolled c ∧
          (c.queryCount 0 : ℝ) ≤ C ∧
          (c.gateCount : ℝ) ≤ C * (n * (Real.log (n / εg)) ^ 2 + Real.log (1 / ε)) ∧
          (n * ℓo : ℝ) ≤ C * (n * (Real.log (n / εg)) ^ 2 + Real.log (1 / ε) + 1) ∧
          ∀ (w p : EuclideanSpace ℝ (Fin n)) (θ : ℝ), ‖w‖ = 1 →
            1 / 10 ≤ |inner ℝ w p| → |inner ℝ w p| ≤ 3 →
            ∀ Htil : (Fin n → Qubits b) → Qubits Vb,
              (∀ x, |fpVal Vb Vf (Htil x) - height w θ p (rho n • gridVec n b x)| ≤ η) →
            ∀ OH : Matrix (Qubits (n * b + Vb + W)) (Qubits (n * b + Vb + W)) ℂ,
              OH ∈ Matrix.unitaryGroup (Qubits (n * b + Vb + W)) ℂ →
              (∀ x, act OH (ket (regBasis n b Vb W x fun _ => false)) =
                ket (regBasis n b Vb W x (Htil x))) →
              open Classical in
              probEvent (act (c.unitary fun _ => OH) (zeroKet m))
                (fun z => ∀ i, |readFp (oa i) fo z - (-(w i) / inner ℝ w p)| ≤ εg) ≥ 3 / 4 := by sorry
