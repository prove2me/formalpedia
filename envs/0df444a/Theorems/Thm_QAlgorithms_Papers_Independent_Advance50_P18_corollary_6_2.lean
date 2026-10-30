-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P18_corollary_6_2
-- name    : QAlgorithms.Papers.Independent.Advance50.P18.corollary_6_2
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T11:53:07.155821+00:00
-- url     : https://prove2.me/theorems/01597b7e-7cf5-40e7-bf09-e596dcbc4209
-- title:
--   Corollary 6.2: optimal entropy for randomizing real product states
-- statement:
--   Let $B$ be the normalized real-qubit circle $\{\cos\theta|0\rangle+\sin\theta|1\rangle:0\le\theta<2\pi\}$. For every $n\ge0$, uniform independent $I/Y$ conjugations give an ancilla-free randomizer of $B^{\otimes n}$ of entropy cost exactly $n$ bits. Conversely, every exact randomizer of that source, allowing any fixed mixed ancillary environment and retaining all of its output, costs at least $n$:
--
--   $$\exists\,\mathcal E:\ H(p_{\mathcal E})=n,\qquad \forall\,\mathcal R:\ H(p_{\mathcal R})\ge n.$$
--
--   Here the quantifiers range over the paper’s finite random-unitary procedures on that product source. Entropy measures the forgotten key, not the entropy increase of the visible message alone. This establishes optimality for real product states.
-- source:
--   Private Quantum Channels and the Cost of Randomizing Quantum Information, arXiv:quant-ph/0003101v2, PDF p. 9, Corollary 6.2: optimal entropy for randomizing real product states

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P18

namespace QAlgorithms.Papers.Independent.Advance50.P18

open scoped ComplexConjugate

noncomputable section

variable {K I A : Type*} [Fintype K] [DecidableEq K]
  [Fintype I] [DecidableEq I] [Fintype A] [DecidableEq A]

/-- PDF p.9, Corollary 6.2: randomizing arbitrary tensor products of real qubits
has attainable entropy cost exactly n, and every full-environment procedure costs at least n. -/
theorem corollary_6_2 (n : ℕ) :
    (∃ E : KeyedUnitaryEnsemble (Qubits n) (Qubits n), E = realPauli n ∧
      BareRandomizes (realProductSource n) E (sourceMixedIdentity (Qubits n)) ∧
      keyEntropy E.p = (n : ℝ)) ∧
    (∀ (a N : ℕ) (E : KeyedUnitaryEnsemble (Fin N) (Qubits n × Qubits a))
      (anc : (Matrix (Qubits a) (Qubits a) ℂ)) (rho0 : (Matrix (Qubits n × Qubits a) (Qubits n × Qubits a) ℂ)),
      ExactSourceRandomization (realProductSource n) E anc rho0 → (n : ℝ) ≤ keyEntropy E.p) := by sorry

end

end QAlgorithms.Papers.Independent.Advance50.P18
