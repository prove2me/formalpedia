-- Prove2me | Theorems.Thm_QAlgorithms_LearningSurvey_servedioGortler_quantum_lower
-- name    : QAlgorithms.LearningSurvey.servedioGortler_quantum_lower
-- status  : Open
-- author  : @Goku
-- created : 2026-10-13T17:55:13.382217+00:00
-- url     : https://prove2.me/theorems/a2b8becb-1a01-4e3b-8f2c-1c4289cc1b1d
-- title:
--   Servedio–Gortler: quantum exact learning needs Ω(max{1/√γ(C), log|C|/n}) queries
-- statement:
--   This is the Servedio–Gortler lower bound on the quantum query complexity of exact learning.
--
--   Let $n\ge 1$ and $N=2^n$. A concept $c:\{0,1\}^n\to\{0,1\}$ is identified with its truth table in $\{0,1\}^N$, and a concept class is a set $C\subseteq\{0,1\}^N$ with $|C|\ge 2$. Let $\gamma(C)$ be the combinatorial parameter of Definition 4.1,
--   $$\gamma(C)=\min_{C'\subseteq C,\ |C'|\ge 2}\ \max_{i\in[N]}\ \min_{b\in\{0,1\}}\frac{|\{c\in C': c_i=b\}|}{|C'|}.$$
--   A quantum exact learner making $T$ queries applies input-independent unitaries interleaved with $T$ applications of the membership oracle $O_c:|x,b\rangle\mapsto|x,b\oplus c(x)\rangle$ (with a workspace of arbitrary finite dimension), measures, and outputs a concept $h$; it is exact for $C$ if $\Pr[h=c]\ge 2/3$ for every target $c\in C$. Then there is an absolute constant $K>0$ such that every such learner satisfies
--   $$T\ \ge\ K\cdot\max\left\{\frac{1}{\sqrt{\gamma(C)}},\ \frac{\log|C|}{n}\right\}.$$
--
--   Together with the classical bounds of Theorem 4.2 this yields the polynomial relation between classical and quantum exact learning (Corollary 4.4).
--
--   **Formalization Note** The logarithm is natural; another base only changes $K$. The learner's internal randomness and any final POVM are absorbed into the start state, the unitaries and a computational-basis measurement on the workspace.
-- source:
--   Srinivasan Arunachalam and Ronald de Wolf, A Survey of Quantum Learning Theory, 2017, v3, PDF p. 9, §4.1.1, Theorem 4.3. https://arxiv.org/pdf/1701.06806v3

import Definitions.Def_QAlgorithms_Defs_LearningHardInstances
set_option autoImplicit false

namespace QAlgorithms.LearningSurvey

universe u

/-- **Theorem 4.3** (Servedio–Gortler; survey p.9). Let `N = 2^n`. Every quantum exact learner for
a concept class `C ⊆ {0,1}^N` makes `Ω(max{1/√γ(C), (log |C|)/n})` membership queries.
The constant `K` is absolute (chosen before `n`, `C`, the workspace and the learner). -/
theorem servedioGortler_quantum_lower :
    ∃ K : ℝ, 0 < K ∧ ∀ (n : ℕ), 1 ≤ n → ∀ (C : Finset (Qubits n → Bool)), 2 ≤ C.card →
      ∀ (W : Type u) [Fintype W] [DecidableEq W] (T : ℕ) (A : QueryAlg (Qubits n) Bool W T)
        (out : (Qubits n × Bool) × W → (Qubits n → Bool)),
        Learning.IsQExactLearner A out C →
          K * max (1 / Real.sqrt (Learning.gammaParam C)) (Real.log (C.card : ℝ) / (n : ℝ)) ≤
            (T : ℝ) := by
  sorry





end QAlgorithms.LearningSurvey
