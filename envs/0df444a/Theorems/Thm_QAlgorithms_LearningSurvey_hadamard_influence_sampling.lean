-- Prove2me | Theorems.Thm_QAlgorithms_LearningSurvey_hadamard_influence_sampling
-- name    : QAlgorithms.LearningSurvey.hadamard_influence_sampling
-- status  : Proved
-- author  : @fizzyinc3
-- created : 2026-10-17T23:11:40.580987+00:00
-- url     : https://prove2.me/theorems/ba965839-a2ee-470f-9114-865c7fab59fd
-- title:
--   Hadamard sampling of Boolean influences: exact repeated-coordinate absence law
-- statement:
--   Let $n,T$ be nonnegative integers. There is a quantum circuit, depending only on $n,T$, over the Hadamard, T and CNOT gate set, with no ancillas and at most $T(n+1)$ gates, with the following property for every Boolean function $f:\{0,1\}^n\to\{0,1\}$.
--
--   Apply the circuit to $T$ independent uniform quantum examples of $f$, and measure all registers in the computational basis. Let $P_f$ be the outcome law and let $Z^{(j)}_i$ be the measured input bit at coordinate $i$ in example register $j$. Define the uniform influence by
--   $$
--   I_i(f)=2^{-n}\sum_x\mathbf1\{f(x\oplus e_i)\ne f(x)\}.
--   $$
--   Then
--   $$
--   \sum_z P_f(z)=1,\qquad
--   \Pr[Z^{(j)}_i=0\text{ for all }j<T]=(1-I_i(f)/2)^T
--   $$
--   for every input coordinate $i$. The same circuit works for every $f$; no junta or relevant-coordinate-set hypothesis is required.
--
--   This is the quantum sampling identity needed to convert coordinate influences into absence probabilities under repeated independent examples.
--
--   **Formalization Note** The statement retains every label outcome and uses the existing explicit block layout of the quantum examples. Accordingly the influence is halved relative to Fourier sampling conditioned on a successful label, as in the survey. The cases $T=0$ and $n=0$ are included.
-- source:
--   Arunachalam and de Wolf, A Survey of Quantum Learning Theory, arXiv:1701.06806v3, PDF p.5 §2.2.2 (Fourier sampling), PDF p.7 §3.2 (uniform quantum examples and the label-success factor 1/2), and PDF p.19, proof of Theorem 5.4 (influence identity and independent repeated-sampling absence probability). https://arxiv.org/pdf/1701.06806v3

import Definitions.Def_QAlgorithms_LearningSurvey_Ch05_Model
set_option autoImplicit false
open scoped BigOperators

theorem QAlgorithms.LearningSurvey.hadamard_influence_sampling (n T : ℕ) :
    ∃ c : QAlgorithms.Circuit QAlgorithms.htcxGateSet (T * (n + 1) + 0),
      c.size ≤ T * (n + 1) ∧
      ∀ f : QAlgorithms.Qubits n → Bool,
        let P := fun z => QAlgorithms.prob
          (QAlgorithms.act c.unitary (QAlgorithms.LearningSurvey.juntaExamplesState n T 0 f)) z
        (∑ z, P z) = 1 ∧
        ∀ i : Fin n,
          (∑ z, if (∀ j : Fin T, QAlgorithms.LearningSurvey.exInput n z j i = false)
            then P z else 0) =
          (1 - (((2 : ℝ)^n)⁻¹ * ∑ x : QAlgorithms.Qubits n,
            if f (Function.update x i (!x i)) ≠ f x then (1 : ℝ) else 0) / 2)^T := by sorry
