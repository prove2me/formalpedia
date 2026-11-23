-- Prove2me | Theorems.Thm_QuantumLTF_Membership_coordinatewise_median_amplification
-- name    : QuantumLTF.Membership.coordinatewise_median_amplification
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T02:30:45.054486+00:00
-- url     : https://prove2.me/theorems/a0da948e-3c20-4d4a-a29f-91a782a6b9f7
-- title:
--   Coherent coordinate-wise median amplification of a fixed-point-output circuit
-- statement:
--   Let $c_0$ be an uncontrolled oracle circuit over one- and two-qubit unitaries, started in $|0\cdots0\rangle$, whose designated wires encode $n$ signed fixed-point outputs. Suppose that against a unitary oracle $O$, one run of $c_0$ produces a vector within coordinate-wise error $\delta$ of a fixed target $g$ with probability at least $3/4$.
--
--   For every $0<\gamma\le1/2$, there is another such oracle circuit which repeats the first circuit independently and coherently computes the coordinate-wise median. Its output has the same fixed-point format and satisfies the same error bound with probability at least $1-\gamma$. If $q_0$ and $s_0$ are respectively the query and gate counts of one run, and each output coordinate uses $\ell_o$ wires, then the amplified circuit uses
--   $$O((q_0+1)\log(1/\gamma))$$
--   oracle calls and
--   $$O((s_0+n\ell_o+1)\log(1/\gamma))$$
--   additional gates. No controlled oracle calls are introduced.
--
--   This is the generic circuit form of the last two paragraphs of the proof of Theorem 3.3: Hoeffding’s inequality bounds the probability that at most half the runs are good by $e^{-R/8}$ for $R$ repetitions, and a strict majority of good vectors forces every coordinate of their median to lie in the desired interval. Reversible linear-time selection accounts for the output-format term $n\ell_o$ in the gate bound.
-- source:
--   Krivcenko–Nguyen–de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, arXiv:2609.40331, proof of Theorem 3.3, p. 30 (PDF p. 31), Eq. (59), median argument, and Eqs. (60)–(62). The statement abstracts precisely that repetition step to an arbitrary one-run fixed-point-output circuit.

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QuantumLTF_Membership_readFp
import Definitions.Def_QuantumLTF_Membership_gates12
import Definitions.Def_QuantumLTF_Membership_Uncontrolled

open QAlgorithms

/-- A generic coherent version of the repetition and coordinate-wise median step in the proof of
Theorem 3.3, p. 30 (PDF p. 31), Eq. (59) and the resource accounting in Eqs. (60)–(62). -/
theorem QuantumLTF.Membership.coordinatewise_median_amplification
    (n a m ℓo fo : ℕ)
    (c₀ : OracleCircuit gates12 (fun _ : Fin 1 => a) m)
    (oa : Fin n → (Fin ℓo ↪ Fin m)) :
    Uncontrolled c₀ →
    ∃ C : ℝ, 0 < C ∧ ∀ γ : ℝ, 0 < γ → γ ≤ 1 / 2 →
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
