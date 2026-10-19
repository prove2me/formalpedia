-- Prove2me | Theorems.Thm_QAlgorithms_LearningSurvey_juntaLearning_quantum_corrected
-- name    : QAlgorithms.LearningSurvey.juntaLearning_quantum_corrected
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-13T17:55:07.321754+00:00
-- url     : https://prove2.me/theorems/620cc592-26a9-4ef6-8712-6ec933f04e59
-- title:
--   Atıcı–Servedio: time-efficient quantum learning of k-juntas (corrected)
-- statement:
--   This is a corrected form of the Atıcı–Servedio theorem on learning juntas from uniform quantum examples.
--
--   A function $f:\{0,1\}^n\to\{0,1\}$ is a $k$-junta if it depends on at most $k$ of its $n$ input bits. A uniform quantum example of $f$ is the $(n+1)$-qubit state $\sum_{x\in\{0,1\}^n}2^{-n/2}|x,f(x)\rangle$; a uniform classical example is a pair $(x,f(x))$ with $x$ uniform on $\{0,1\}^n$. The error of a hypothesis $h$ is $\Pr_{x}[h(x)\neq f(x)]$ for uniform $x$.
--
--   Time is measured in the following hybrid cost model, which is the one the source's proof sketch counts in. A learner (1) applies a circuit over the gate set $\{H,T,\mathrm{CNOT}\}$ to $T_Q$ uniform quantum examples and some ancillas in $|0\rangle$ and measures every qubit in the computational basis; (2) maps the outcome by a Boolean circuit of AND/OR/NOT gates to a set $V\subseteq[n]$ of variables; (3) reads $T_C$ uniform classical examples and outputs the truth-table hypothesis $h(x)=f(x_j)$ for the first example $x_j$ that agrees with $x$ on $V$ ($h(x)=0$ if there is none). Its time is the number of quantum gates, plus the number of measured qubits, plus the number of Boolean gates, plus $T_C$ (one unit per classical example, which is read and written into the table cell indexed by its $V$-bits), plus $2^{|V|}$ table cells (worst case over the outcomes).
--
--   For every $\delta\in(0,1)$ there is a constant $C>0$ such that for all $n,k$ with $2\le k\le n$ and all $\varepsilon\in(0,1/2]$ there is such a learner with
--
--   $$
--   T_Q\le C\,\frac{k\log k}{\varepsilon},\qquad T_C\le C\,2^k\log\frac1\varepsilon,\qquad \mathrm{time}\le C\Big(\frac{nk\log k}{\varepsilon}+2^k\log\frac1\varepsilon\Big),
--   $$
--
--   which, for every $k$-junta $f$, outputs with probability at least $1-\delta$ (over the measurement outcomes and the classical examples) a hypothesis of error at most $\varepsilon$.
--
--   The theorem shows that quantum examples remove the $n^{\Theta(k)}$ search over candidate variable sets that the best known classical learners need, which is why juntas are a notorious bottleneck classically.
--
--   **Formalization Note** The source states no cost model, no confidence parameter, and $O(2^k)$ classical examples. The cost model above, the fixed-confidence reading (constants depend on $\delta$ only), and the $O(2^k\log(1/\varepsilon))$ classical examples of the source's own proof sketch are the corrections. The thresholds $k\ge2$ and $\varepsilon\le1/2$ make $\log k$ and $\log(1/\varepsilon)$ positive.
-- source:
--   Srinivasan Arunachalam and Ronald de Wolf, A Survey of Quantum Learning Theory, 2017, v3, PDF p. 19, Theorem 5.4. https://arxiv.org/pdf/1701.06806v3

import Definitions.Def_QAlgorithms_Defs_Learning
import Definitions.Def_QAlgorithms_LearningSurvey_Ch05_Model
set_option autoImplicit false

namespace QAlgorithms.LearningSurvey










/-- Corrected statement. Survey p.19, Theorem 5.4 ([AS09]), as printed: "There exists a quantum
algorithm for learning `k`-juntas under the uniform distribution that uses `O(k log(k)/ε)` uniform
quantum examples, `O(2^k)` uniform classical examples, and `O(nk log(k)/ε + 2^k log(1/ε))` time."

Changed: (1) the time is measured in the explicit cost model `JuntaHybridLearner.cost` (quantum
gates from `{H, T, CNOT}`, measured qubits, Boolean gates, one unit per classical example and per
truth-table cell), the model the proof sketch's count uses; (2) the classical-example bound is
`O(2^k log(1/ε))`, as used in the proof sketch, instead of the printed `O(2^k)`; (3) "with high
probability" is read as: for every fixed confidence `1 − δ`, `δ ∈ (0,1)`, with the constant `C`
depending on `δ` only (the bounds carry no `δ`). The `O`-thresholds are `k ≥ 2` and `ε ≤ 1/2`, where
`log k` and `log(1/ε)` are positive.

Why: the source fixes no cost model, and the printed time bound fails in a bit-cost or word-RAM
model (reading the `V`-bits of `2^k log(1/ε)` classical examples alone costs `k 2^k log(1/ε)`); the
confidence is never given; and the printed `O(2^k)` classical examples contradicts the proof
sketch, which needs `O(2^k log(1/ε))` to see `1 − ε/2` of the `2^{|V|}` table cells. -/
theorem juntaLearning_quantum_corrected :
    ∀ δ : ℝ, 0 < δ → δ < 1 → ∃ C : ℝ, 0 < C ∧
      ∀ n k : ℕ, 2 ≤ k → k ≤ n → ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
        ∃ L : JuntaHybridLearner n,
          (L.TQ : ℝ) ≤ C * ((k : ℝ) * Real.log k / ε) ∧
          (L.TC : ℝ) ≤ C * ((2 : ℝ) ^ k * Real.log (1 / ε)) ∧
          (L.cost : ℝ) ≤ C * ((n : ℝ) * k * Real.log k / ε + (2 : ℝ) ^ k * Real.log (1 / ε)) ∧
          ∀ f : Qubits n → Bool, IsJunta f k → L.successProb f ε ≥ 1 - δ := by
  sorry

end QAlgorithms.LearningSurvey
