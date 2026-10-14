-- Prove2me | Theorems.Thm_QAlgorithms_LearningSurvey_quantumPAC_sampleLowerBound
-- name    : QAlgorithms.LearningSurvey.quantumPAC_sampleLowerBound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-13T17:55:47.987984+00:00
-- url     : https://prove2.me/theorems/8dbf7da8-612a-4211-91b9-6204bd286207
-- title:
--   Quantum PAC learning needs Ω(d/ε + log(1/δ)/ε) quantum examples
-- statement:
--   This is the optimal lower bound on the quantum sample complexity of PAC learning, with the threshold on the VC dimension that the proof requires.
--
--   Let $C$ be a concept class of Boolean functions $c:\{0,1\}^n\to\{0,1\}$ with VC dimension $d+1$. For a distribution $D$ on $\{0,1\}^n$ and $c\in C$, a quantum example is the state $\sum_x\sqrt{D(x)}\,|x,c(x)\rangle$. An $(\varepsilon,\delta)$-quantum PAC learner for $C$ with $T$ examples is a POVM $\{M_h\}$ on $T$ copies of the quantum example, with one outcome for every hypothesis $h:\{0,1\}^n\to\{0,1\}$, such that for every $c\in C$ and every distribution $D$ the outcome $h$ satisfies $\Pr_{x\sim D}[h(x)\neq c(x)]\le\varepsilon$ with probability at least $1-\delta$.
--
--   There are an absolute constant $K>0$ and a threshold $d_0$ such that for all $n$, all $d\ge d_0$, every concept class $C$ of VC dimension $d+1$, all $\delta\in(0,1/2)$ and $\varepsilon\in(0,1/20)$, every $(\varepsilon,\delta)$-quantum PAC learner for $C$ uses
--
--   $$
--   T\ \ge\ K\Big(\frac{d}{\varepsilon}+\frac{1}{\varepsilon}\log\frac{1}{\delta}\Big)
--   $$
--
--   examples.
--
--   Together with the classical upper bound, this shows that quantum examples give no advantage in the distribution-free PAC model.
--
--   **Formalization Note** The source prints the bound for every $d$; at small $d$ and $\delta$ close to $1/2$ it is false (for two concepts differing at one point, one quantum example measured in the computational basis, with a fair coin when the distinguishing point is not seen, is an $(\varepsilon, 1/2-\varepsilon/2)$-learner). The threshold $d_0$ is the source's own "$d$ a sufficiently large constant" from the proof. Ancillas and internal randomness are absorbed into the POVM.
-- source:
--   Srinivasan Arunachalam and Ronald de Wolf, A Survey of Quantum Learning Theory, 2017, v3, PDF p. 13, Theorem 4.12. https://arxiv.org/pdf/1701.06806v3

import Definitions.Def_QAlgorithms_Defs_LearningHardInstances
set_option autoImplicit false

namespace QAlgorithms.LearningSurvey

open MeasureTheory QAlgorithms.Learning

/-- survey p.13, Theorem 4.12 ([AW17]): optimal quantum PAC sample-complexity lower bound.
Let `C` be a concept class on `{0,1}^n` with VC dimension `d + 1`. For every `δ ∈ (0, 1/2)` and
`ε ∈ (0, 1/20)`, every `(ε, δ)`-quantum PAC learner for `C` (a POVM on `T` copies of the quantum
example, one outcome per hypothesis, correct for every `c ∈ C` and every distribution `D`) uses
`T = Ω(d/ε + (1/ε) log(1/δ))` copies.

Corrected statement (trap 30): the `Ω` carries a threshold `d₀` on `d` (the source's proof needs
"`d` a sufficiently large constant", p.13; this is also the run's asymptotic convention). Without
it the printed statement is false: for `C = {c₁, c₂}` differing at one point (VC dimension 1,
`d = 0`), one copy measured in the computational basis, with a fair coin when the distinguishing
point is not seen, is an `(ε, 1/2 − ε/2)`-learner, while `K log(1/δ)/ε → ∞` as `ε → 0`. -/
theorem quantumPAC_sampleLowerBound :
    ∃ K : ℝ, 0 < K ∧ ∃ d₀ : ℕ, ∀ (n d : ℕ) (C : Finset (Qubits n → Bool)), d₀ ≤ d →
      vcDimClass C = d + 1 →
      ∀ δ ε : ℝ, 0 < δ → δ < 1 / 2 → 0 < ε → ε < 1 / 20 →
      ∀ (T : ℕ) (M : (Qubits n → Bool) →
          Matrix (Fin T → Qubits n × Bool) (Fin T → Qubits n × Bool) ℂ),
        IsQPACLearner C ε δ T M →
        K * ((d : ℝ) / ε + (1 / ε) * Real.log (1 / δ)) ≤ (T : ℝ) := by sorry




end QAlgorithms.LearningSurvey
