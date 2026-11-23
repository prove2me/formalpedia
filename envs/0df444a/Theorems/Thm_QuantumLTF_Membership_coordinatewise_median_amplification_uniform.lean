-- Prove2me | Theorems.Thm_QuantumLTF_Membership_coordinatewise_median_amplification_uniform
-- name    : QuantumLTF.Membership.coordinatewise_median_amplification_uniform
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T02:32:53.732784+00:00
-- url     : https://prove2.me/theorems/62500608-be2e-4ca3-b8e3-f9f80d22ec5a
-- title:
--   Uniform coherent coordinate-wise median amplification
-- statement:
--   There is a universal constant $C>0$ with the following coherent median-amplification property.
--
--   Let $c_0$ be an uncontrolled oracle circuit over one- and two-qubit unitaries, started in $|0\cdots0\rangle$, whose designated wires encode $n$ signed fixed-point outputs. Suppose that against a unitary oracle $O$, one run produces a vector within coordinate-wise error $\delta$ of a fixed target $g$ with probability at least $3/4$.
--
--   For every $0<\gamma\le1/2$, there is an uncontrolled circuit which independently repeats $c_0$ and coherently computes the coordinate-wise median. Its output has the same fixed-point format and satisfies the same error bound with probability at least $1-\gamma$. If $q_0$ and $s_0$ are respectively the query and gate counts of one run, and each output coordinate uses $\ell_o$ wires, then the amplified circuit uses at most
--   $$C(q_0+1)\log(1/\gamma)$$
--   oracle calls and at most
--   $$C(s_0+n\ell_o+1)\log(1/\gamma)$$
--   additional gates.
--
--   Crucially, $C$ is fixed before the input circuit and all numerical parameters. This is the uniform version of the repetition argument in the proof of Theorem 3.3: with $R=\Theta(\log(1/\gamma))$ odd repetitions, Hoeffding’s inequality makes the probability of having no strict majority of good runs at most $\gamma$; a strict majority of good runs makes every median coordinate accurate. Reversible selection and repetition give the stated resource bounds.
-- source:
--   Krivcenko–Nguyen–de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, arXiv:2609.40331, proof of Theorem 3.3, p. 30 (PDF p. 31), Eq. (59), median argument, and Eqs. (60)–(62). This abstracts the uniform big-O constant of that step.

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QuantumLTF_Membership_readFp
import Definitions.Def_QuantumLTF_Membership_gates12
import Definitions.Def_QuantumLTF_Membership_Uncontrolled

open QAlgorithms

/-- The uniform-constant form of the generic coherent repetition and coordinate-wise median step in
the proof of Theorem 3.3, p. 30 (PDF p. 31), Eq. (59) and Eqs. (60)–(62). -/
theorem QuantumLTF.Membership.coordinatewise_median_amplification_uniform :
    ∃ C : ℝ, 0 < C ∧ ∀ (n a m ℓo fo : ℕ)
      (c₀ : OracleCircuit gates12 (fun _ : Fin 1 => a) m)
      (oa : Fin n → (Fin ℓo ↪ Fin m)), Uncontrolled c₀ →
      ∀ γ : ℝ, 0 < γ → γ ≤ 1 / 2 →
      ∃ (m' : ℕ) (c : OracleCircuit gates12 (fun _ : Fin 1 => a) m')
        (out : Fin n → (Fin ℓo ↪ Fin m')),
        Uncontrolled c ∧
        (c.queryCount 0 : ℝ) ≤ C * (c₀.queryCount 0 + 1) * Real.log (1 / γ) ∧
        (c.gateCount : ℝ) ≤ C * (c₀.gateCount + n * ℓo + 1) * Real.log (1 / γ) ∧
        ∀ OH : Matrix (Qubits a) (Qubits a) ℂ,
          OH ∈ Matrix.unitaryGroup (Qubits a) ℂ →
          ∀ (g : Fin n → ℝ) (δ : ℝ),
            (3 / 4 : ℝ) ≤ probEvent (act (c₀.unitary fun _ => OH) (zeroKet m))
              (fun z => ∀ i, |readFp (oa i) fo z - g i| ≤ δ) →
            open Classical in
            probEvent (act (c.unitary fun _ => OH) (zeroKet m'))
              (fun z => ∀ i, |readFp (out i) fo z - g i| ≤ δ) ≥ 1 - γ := by sorry
