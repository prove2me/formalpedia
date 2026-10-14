-- Prove2me | Theorems.Thm_QAlgorithms_LearningSurvey_kothari_quantum_exact_upper
-- name    : QAlgorithms.LearningSurvey.kothari_quantum_exact_upper
-- status  : Open
-- author  : @Goku
-- created : 2026-10-13T17:55:48.899733+00:00
-- url     : https://prove2.me/theorems/3a8a319a-bfde-497f-9c2e-e0437d3e7e2f
-- title:
--   Kothari: quantum exact learning with O(√((1/γ)/log(1/γ))·log|C|) queries
-- statement:
--   This is Kothari's upper bound on quantum exact learning in terms of the combinatorial parameter $\gamma(C)$.
--
--   Let $N=2^n$ and let $C\subseteq\{0,1\}^N$ be a concept class with $|C|\ge 2$, and let $\gamma(C)$ be as in Definition 4.1. There is an absolute constant $K>0$ such that for every such $C$ there is a quantum exact learner for $C$ (input-independent unitaries interleaved with $T$ queries to $O_c:|x,b\rangle\mapsto|x,b\oplus c(x)\rangle$, outputting $h=c$ with probability at least $2/3$ for every target $c\in C$) with
--   $$T\ \le\ K\sqrt{\frac{1/\gamma(C)}{\log(1/\gamma(C))}}\ \log|C| .$$
--
--   It nearly matches the $\Omega(1/\sqrt{\gamma(C)})$ lower bound of Theorem 4.3 and resolved a conjecture of Hunziker et al.
--
--   **Formalization Note** Since $|C|\ge 2$ forces $0<\gamma(C)\le 1/2$, the logarithm $\log(1/\gamma(C))\ge\log 2$ is positive. The logarithm is natural; the base only changes $K$.
-- source:
--   Srinivasan Arunachalam and Ronald de Wolf, A Survey of Quantum Learning Theory, 2017, v3, PDF p. 12, §4.1.2, Theorem 4.8. https://arxiv.org/pdf/1701.06806v3

import Definitions.Def_QAlgorithms_Defs_LearningHardInstances
set_option autoImplicit false

namespace QAlgorithms.LearningSurvey

universe u





/-- **Theorem 4.8** (Kothari; survey p.12). For every concept class `C ⊆ {0,1}^N` (`N = 2^n`,
`|C| ≥ 2`, the domain of `γ`), there is a quantum exact learner for `C` using
`O(√((1/γ(C)) / log(1/γ(C))) · log |C|)` quantum membership queries. The constant `K` is absolute;
the learner is chosen after `C` but before the target concept. -/
theorem kothari_quantum_exact_upper :
    ∃ K : ℝ, 0 < K ∧ ∀ (n : ℕ) (C : Finset (Qubits n → Bool)), 2 ≤ C.card →
      ∃ (w T : ℕ) (A : QueryAlg (Qubits n) Bool (Fin w) T)
        (out : (Qubits n × Bool) × Fin w → (Qubits n → Bool)),
        Learning.IsQExactLearner A out C ∧
          (T : ℝ) ≤ K * Real.sqrt ((1 / Learning.gammaParam C) /
            Real.log (1 / Learning.gammaParam C)) * Real.log (C.card : ℝ) := by
  sorry

end QAlgorithms.LearningSurvey
