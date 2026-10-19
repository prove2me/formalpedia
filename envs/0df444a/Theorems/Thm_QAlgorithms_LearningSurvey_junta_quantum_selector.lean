-- Prove2me | Theorems.Thm_QAlgorithms_LearningSurvey_junta_quantum_selector
-- name    : QAlgorithms.LearningSurvey.junta_quantum_selector
-- status  : Proved
-- author  : @fizzyinc3
-- created : 2026-10-17T22:38:03.535979+00:00
-- url     : https://prove2.me/theorems/ee371482-3c07-4637-9235-2977a59de9ae
-- title:
--   Quantum Fourier samples select a bounded variable set with small expected within-cell disagreement
-- statement:
--   This is the variable-selection stage in the quantum junta learner of Atıcı and Servedio.
--
--   For a Boolean function $f$ on $n$ bits and a variable set $V$, let
--   $$
--   D_V(f)=\mathbb E_x\Pr_y[f(y)\ne f(x)\mid y|_V=x|_V],
--   $$
--   where inputs are uniform. Each restriction cell has probability $2^{-|V|}$.
--
--   There is an absolute constant $C>0$ such that, for $2\le k\le n$ and $0<\eta\le1/2$, a circuit over Hadamard, T and CNOT gates, followed by a well-formed Boolean circuit, selects a set $V$ using
--   $$
--   T_Q\le C\frac{k\log k}{\eta},\qquad
--   \text{gates + measured qubits + Boolean gates}\le C\frac{nk\log k}{\eta}.
--   $$
--   Its output has at most $k$ selected variables for every bit string, including measurement outcomes of probability zero. For every $k$-junta, its measurement probabilities sum to one and
--   $$
--   \mathbb E_V D_V(f)\le\eta.
--   $$
--   This isolates quantum variable selection from the subsequent classical table learner. It states the expected-disagreement estimate used to control conflicting labels when a few influential variables are missed.
--
--   **Formalization Note** The quantum and Boolean circuits are packaged in the existing hybrid learner with zero classical examples. The worst-case bound on the output mask can be enforced by truncating to the first $k$ variables; for a junta, unions of Fourier supports already have at most $k$ variables. The expectation form follows the source's missing-influence estimate and uses no accuracy-dependent confidence requirement.
-- source:
--   Arunachalam and de Wolf, A Survey of Quantum Learning Theory, arXiv:1701.06806v3, PDF p.19, Theorem 5.4, first part of the proof sketch (Fourier sampling and the union of sampled supports). https://arxiv.org/pdf/1701.06806v3

import Definitions.Def_QAlgorithms_LearningSurvey_Ch05_Model
set_option autoImplicit false
open scoped BigOperators

theorem QAlgorithms.LearningSurvey.junta_quantum_selector :
    ∃ C : ℝ, 0 < C ∧ ∀ n k : ℕ, 2 ≤ k → k ≤ n →
      ∀ η : ℝ, 0 < η → η ≤ 1 / 2 → ∃ L : QAlgorithms.LearningSurvey.JuntaHybridLearner n,
        L.TC = 0 ∧
        (L.TQ : ℝ) ≤ C * ((k : ℝ) * Real.log k / η) ∧
        ((L.circ.size + (L.TQ * (n + 1) + L.anc) + L.post.size : ℕ) : ℝ) ≤
          C * ((n : ℝ) * k * Real.log k / η) ∧
        (∀ z, QAlgorithms.hammingWeight (L.post.eval z) ≤ k) ∧
        ∀ f : QAlgorithms.Qubits n → Bool, QAlgorithms.LearningSurvey.IsJunta f k →
          (∑ z, QAlgorithms.prob
            (QAlgorithms.act L.circ.unitary (QAlgorithms.LearningSurvey.juntaExamplesState n L.TQ L.anc f)) z) = 1 ∧
          (∑ z, QAlgorithms.prob
            (QAlgorithms.act L.circ.unitary (QAlgorithms.LearningSurvey.juntaExamplesState n L.TQ L.anc f)) z *
            (((2 : ℝ)^n)⁻¹ * ∑ x : QAlgorithms.Qubits n,
              (((2 : ℝ)^n)⁻¹ * ∑ y : QAlgorithms.Qubits n,
                if (∀ i, L.post.eval z i = true → y i = x i) ∧ f y ≠ f x then (1 : ℝ) else 0) *
              (2 : ℝ)^QAlgorithms.hammingWeight (L.post.eval z))) ≤ η := by sorry
