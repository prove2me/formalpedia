-- Prove2me | Theorems.Thm_QAlgorithms_LearningSurvey_junta_fourier_influence_sampler
-- name    : QAlgorithms.LearningSurvey.junta_fourier_influence_sampler
-- status  : Proved
-- author  : @fizzyinc3
-- created : 2026-10-17T22:52:05.401987+00:00
-- url     : https://prove2.me/theorems/ee9b18b0-5c51-4291-b88a-f1a168f05a01
-- title:
--   Fourier sampling: relevant-variable support, missing-influence tail and resampling bound
-- statement:
--   Let $f:\{0,1\}^n\to\{0,1\}$ depend only on a coordinate set $S$, and let
--   $$
--   I_i(f)=\Pr_x[f(x\oplus e_i)\ne f(x)]
--   $$
--   for uniform $x$. For every positive number $T$ of quantum examples, there is a circuit, independent of $f$ and $S$, using at most $T(n+1)$ gates from the Hadamard, T and CNOT gate set and no ancillas. Write $P$ for its computational-basis measurement law on $T$ uniform quantum examples, and let $V(z)$ be the union of the supports of the measured data registers.
--
--   The law is normalized. Every outcome with positive probability satisfies $V(z)\subseteq S$, and for every $i\in S$,
--   $$
--   0\le I_i(f)\le1,\qquad
--   \Pr_z[i\notin V(z)]\le(1-I_i(f)/2)^T.
--   $$
--   Moreover, for every fixed coordinate mask $W$, the within-cell disagreement satisfies
--   $$
--   \mathbb E_x\Pr_y[f(y)\ne f(x)\mid y|_W=x|_W]
--   \le\sum_{i\in S\setminus W}I_i(f),
--   $$
--   where inputs are uniform. This is the Fourier-sampling and coordinate-resampling contract used to pass from missing influences to expected prediction error.
--
--   **Formalization Note** The register layout and quantum example amplitudes are those of the existing junta-learning model. The factor $1/2$ retains all measurement outcomes of the label qubits, rather than conditioning on a successful label. Zero-probability outcomes are excluded only from the support assertion, not from the normalization or tail bounds.
-- source:
--   Arunachalam and de Wolf, A Survey of Quantum Learning Theory, arXiv:1701.06806v3, PDF p.5 §2.2.2 (Fourier sampling) and PDF p.19, Theorem 5.4 proof sketch (influence identity, supported Fourier samples and missing-influence probability). https://arxiv.org/pdf/1701.06806v3

import Definitions.Def_QAlgorithms_LearningSurvey_Ch05_Model
set_option autoImplicit false
open scoped BigOperators

theorem QAlgorithms.LearningSurvey.junta_fourier_influence_sampler (n T : ℕ) (hT : 0 < T) :
    ∃ c : QAlgorithms.Circuit QAlgorithms.htcxGateSet (T * (n + 1) + 0),
      c.size ≤ T * (n + 1) ∧
      ∀ (f : QAlgorithms.Qubits n → Bool) (S : Finset (Fin n)),
        (∀ x y : QAlgorithms.Qubits n, (∀ i ∈ S, x i = y i) → f x = f y) →
        let P := fun z => QAlgorithms.prob
          (QAlgorithms.act c.unitary (QAlgorithms.LearningSurvey.juntaExamplesState n T 0 f)) z
        let V := fun z i => decide (∃ j : Fin T, QAlgorithms.LearningSurvey.exInput n z j i = true)
        let I := fun i : Fin n => ((2 : ℝ)^n)⁻¹ * ∑ x : QAlgorithms.Qubits n,
          if f (Function.update x i (!x i)) ≠ f x then (1 : ℝ) else 0
        (∑ z, P z) = 1 ∧
        (∀ z, P z ≠ 0 → ∀ i, V z i = true → i ∈ S) ∧
        (∀ i ∈ S, 0 ≤ I i ∧ I i ≤ 1 ∧
          (∑ z, if V z i = false then P z else 0) ≤ (1 - I i / 2)^T) ∧
        (∀ W : QAlgorithms.Qubits n,
          (((2 : ℝ)^n)⁻¹ * ∑ x : QAlgorithms.Qubits n,
            (((2 : ℝ)^n)⁻¹ * ∑ y : QAlgorithms.Qubits n,
              if (∀ i, W i = true → y i = x i) ∧ f y ≠ f x then (1 : ℝ) else 0) *
            (2 : ℝ)^QAlgorithms.hammingWeight W) ≤
          ∑ i ∈ S, if W i = true then 0 else I i) := by sorry
