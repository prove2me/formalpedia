-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P56_tensor_fourier_formula
-- name    : QAlgorithms.Papers.Independent.Information100.P56.tensor_fourier_formula
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T12:25:02.834158+00:00
-- url     : https://prove2.me/theorems/54a53cdb-42de-4944-a0bd-a2ad3d4021a1
-- title:
--   Section VI D, Eqs.(56)–(59): tensor-output Fourier formula
-- statement:
--   Let the input alphabet be finite and nonempty, and let Bob and Eve have nonzero finite-dimensional output spaces. Each channel output is a positive semidefinite matrix of trace one. Entropies and information rates use natural logarithms, with $0\log0=0$. In the hybrid binary channel, Bob has the binary symmetric channel of crossover $q$, while Eve receives $|\psi_b\rangle=\sqrt{q^{\prime}}|0\rangle+(-1)^b\sqrt{1-q^{\prime}}|1\rangle$. Here $q,q^{\prime}\in[0,1]$, and $x$ is the probability of input symbol $1$. Write $h$ for natural binary entropy. For $n\ge1$ and any law $P$ on $\mathbb Z_2^n$, Bob's average is diagonal with probabilities
--
--   $$P_B(y)=\sum_gP(g)q^{|y\oplus g|}(1-q)^{n-|y\oplus g|}.$$
--
--   Its entropy is the Shannon entropy of these weights. Define $c_P(d)=\sum_gP(g)(-1)^{g\cdot d}$, $w_j=(q^{\prime})^{n-|j|}(1-q^{\prime})^{|j|}$, and $D_{jj}=\sqrt{w_j}$. Eve's average is
--
--   $$D[c_P(j\oplus k)]_{j,k}D,\qquad c_P(0)=1.$$
--
--   The Walsh transform is unnormalized. For the two-use table $P=(t_1,(1-t_1-t_2+t_3)/2,(1-t_1-t_2-t_3)/2,t_2)$ in order $(00,01,10,11)$, its coefficients are $c_P(10)=t_1-t_2+t_3$, $c_P(01)=t_1-t_2-t_3$, and $c_P(11)=2t_1+2t_2-1$. Zero weights require no inverse matrix.
-- source:
--   From Symmetry to Secrecy: Covariant Classical--Quantum Wiretap Channels, arXiv:2610.03580v1, PDF p. 16, Section VI D, Eqs.(56)–(59): tensor-output Fourier formula

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P56

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P56

open scoped ComplexConjugate ComplexOrder Matrix

attribute [local instance] Classical.propDecidable

/-- Section VI D, p.16, Eqs.(56)–(59): physical product outputs and unnormalized
Walsh representation, also at zero weights. The entry formula specifies the whole matrix. -/
theorem tensor_fourier_formula (n : ℕ) (hn : 1 ≤ n) (q qprime : ℝ)
    (hq : q ∈ Set.Icc (0 : ℝ) 1) (hqp : qprime ∈ Set.Icc (0 : ℝ) 1)
    (P : QAlgorithms.Qubits n → ℝ) (hP : IsLaw P) :
    (∀ y z, average (productOutput n (hybridBob q)) P y z =
      if y = z then ((∑ g, P g *
        q ^ QAlgorithms.hammingWeight (fun i => Bool.xor (y i) (g i)) *
        (1 - q) ^ (n - QAlgorithms.hammingWeight (fun i => Bool.xor (y i) (g i))) : ℝ) : ℂ)
      else 0) ∧
    (∀ j k, average (productOutput n (hybridEve qprime)) P j k =
      ((Real.sqrt (eveWeight n qprime j) * walsh P (fun i => Bool.xor (j i) (k i)) *
        Real.sqrt (eveWeight n qprime k) : ℝ) : ℂ)) ∧
    walsh P (fun _ => false) = 1 ∧
    (entropy (average (productOutput n (hybridBob q)) P) =
      - ∑ y : QAlgorithms.Qubits n, let py := ∑ g, P g *
          q ^ QAlgorithms.hammingWeight (fun i => Bool.xor (y i) (g i)) *
          (1 - q) ^ (n - QAlgorithms.hammingWeight (fun i => Bool.xor (y i) (g i)))
        py * Real.log py) ∧
    (∀ (Q : QAlgorithms.Qubits 2 → ℝ) (t1 t2 t3 : ℝ),
      IsLaw Q →
      (∀ z, Q z = (![t1, (1 - t1 - t2 + t3) / 2,
        (1 - t1 - t2 - t3) / 2, t2] (QAlgorithms.bitsEquivFin 2 z))) →
      walsh Q ![true, false] = t1 - t2 + t3 ∧
      walsh Q ![false, true] = t1 - t2 - t3 ∧
      walsh Q ![true, true] = 2 * t1 + 2 * t2 - 1) := by sorry

end QAlgorithms.Papers.Independent.Information100.P56

end
