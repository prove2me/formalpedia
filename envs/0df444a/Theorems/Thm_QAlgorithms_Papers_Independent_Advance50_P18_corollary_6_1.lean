-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P18_corollary_6_1
-- name    : QAlgorithms.Papers.Independent.Advance50.P18.corollary_6_1
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T11:52:23.221647+00:00
-- url     : https://prove2.me/theorems/d70991e7-0c76-4373-97dc-82f3d1e831a1
-- title:
--   Corollary 6.1: optimal entropy for randomizing arbitrary quantum states
-- statement:
--   For every nonnegative integer $n$, there is a randomization procedure on arbitrary $n$-qubit states with entropy cost exactly $2n$ bits: choose a tensor Pauli uniformly, apply it without an ancillary environment, and forget the key. Every density matrix then gives the same output $I_{2^n}/2^n$. Conversely, every valid finite random-unitary procedure, allowing any fixed mixed ancillary environment and retaining its full output, has cost at least $2n$:
--
--   $$\exists\,\mathcal E:\ H(p_{\mathcal E})=2n,\qquad \forall\,\mathcal R:\ H(p_{\mathcal R})\ge2n.$$
--
--   The quantifiers range over the exact source-randomizing procedures just described. Cost is the entropy of the forgotten classical choice. This is an attained optimum, with no infimum convention or thermodynamic work formula required.
-- source:
--   Private Quantum Channels and the Cost of Randomizing Quantum Information, arXiv:quant-ph/0003101v2, PDF p. 9, Corollary 6.1: optimal entropy for randomizing arbitrary quantum states

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P18

namespace QAlgorithms.Papers.Independent.Advance50.P18

open scoped ComplexConjugate

noncomputable section

variable {K I A : Type*} [Fintype K] [DecidableEq K]
  [Fintype I] [DecidableEq I] [Fintype A] [DecidableEq A]

/-- PDF p.9, Corollary 6.1: randomizing all n-qubit states has attainable entropy
cost exactly 2n, and every procedure in the full-environment model costs at least 2n. -/
theorem corollary_6_1 (n : ℕ) :
    (∃ E : KeyedUnitaryEnsemble (Fin n → Fin 4) (Qubits n), E = fullPauli n ∧
      BareRandomizes (allPure (Qubits n)) E (sourceMixedIdentity (Qubits n)) ∧
      keyEntropy E.p = 2 * (n : ℝ) ∧
      ∀ rho : (Matrix (Qubits n) (Qubits n) ℂ), IsDensityMatrix rho →
        encrypt E rho = sourceMixedIdentity (Qubits n)) ∧
    (∀ (a N : ℕ) (E : KeyedUnitaryEnsemble (Fin N) (Qubits n × Qubits a))
      (anc : (Matrix (Qubits a) (Qubits a) ℂ)) (rho0 : (Matrix (Qubits n × Qubits a) (Qubits n × Qubits a) ℂ)),
      ExactSourceRandomization (allPure (Qubits n)) E anc rho0 → 2 * (n : ℝ) ≤ keyEntropy E.p) := by sorry

end

end QAlgorithms.Papers.Independent.Advance50.P18
