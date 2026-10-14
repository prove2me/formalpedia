-- Prove2me | Theorems.Thm_QAlgorithms_Arunachalam_qpac_lower_bound_log
-- name    : QAlgorithms.Arunachalam.qpac_lower_bound_log
-- status  : Open
-- author  : @Goku
-- created : 2026-10-13T17:55:06.367897+00:00
-- url     : https://prove2.me/theorems/59491b4a-4e59-439d-9531-3fdbea3b25cc
-- title:
--   Quantum PAC learners of a non-trivial class need Ω(log(1/δ)/ε) examples
-- statement:
--   Let $C\subseteq\{c:\{0,1\}^n\to\{0,1\}\}$ be a non-trivial concept class: $C$ has at least two concepts and is not of the form $\{c,1-c\}$. A quantum example for a concept $c$ and a distribution $D$ on $\{0,1\}^n$ is the state $\sum_x\sqrt{D(x)}\,|x,c(x)\rangle$. An $(\varepsilon,\delta)$-PAC quantum learner using $T$ examples is a measurement (POVM) on $T$ copies of this state, with outcomes hypotheses $h:\{0,1\}^n\to\{0,1\}$, such that for every $c\in C$ and every distribution $D$ it outputs an $h$ with $\Pr_{x\sim D}[h(x)\ne c(x)]\le\varepsilon$ with probability at least $1-\delta$.
--
--   For every $\delta_0\in(0,1/2)$ there is a constant $C_0>0$ such that for all $n$, all non-trivial $C$, all $\delta\in(0,\delta_0]$, all $\varepsilon\in(0,1/4)$ and every $(\varepsilon,\delta)$-PAC quantum learner for $C$ using $T$ examples,
--
--   $$
--   T\ \ge\ C_0\,\frac{1}{\varepsilon}\log\frac1\delta .
--   $$
--
--   This is the concept-class-independent part of the optimal PAC sample complexity lower bounds, both quantum and classical.
--
--   **Formalization Note** The source asserts the bound with one constant for all $\delta\in(0,1/2)$; this is false as $\delta\to1/2$ (one computational-basis measurement of one example already succeeds with probability $1/2+\varepsilon/2$ on $\{0,1_x\}$), so the constant is uniform over $\delta\le\delta_0$ for each fixed $\delta_0<1/2$, which is what the proof's bound $(1-p)^T\le2\sqrt{\delta(1-\delta)}$ gives. A learner using fewer than $T$ examples is covered by ignoring the extra copies.
-- source:
--   Srinivasan Arunachalam, Quantum Algorithms and Learning Theory — Part II, 2018 thesis, ILLC DS-2018-08, PDF p. 163, Lemma 7.4.1. https://ir.cwi.nl/pub/27536/Thesis_S_Arunachalam

import Definitions.Def_QAlgorithms_Defs_Learning
set_option autoImplicit false

namespace QAlgorithms.Arunachalam

open QAlgorithms.Learning


/-- Arunachalam p.163, Lemma 7.4.1 ([AS05]): for a non-trivial concept class
`C ⊆ {c : {0,1}^n → {0,1}}` (footnote 5: neither a single concept nor a pair of complementary
concepts), every `(ε, δ)`-PAC quantum learner for `C` with `ε ∈ (0, 1/4)` uses
`Ω((1/ε) log(1/δ))` quantum examples.

Corrected statement (trap 30): with one constant for all `δ ∈ (0, 1/2)` the lemma is false (a
single computational-basis measurement of one example succeeds with probability `1/2 + ε/2` on
`C = {0, 1_{x}}`, so `δ = 1/2 − ε/2` needs `T = 1` while `log(1/δ)/ε → ∞`). The proof's bound
`(1 − p)^T ≤ 2√(δ(1 − δ))` gives `Ω(log(1/δ)/ε)` uniformly for `δ ∈ (0, δ₀]` with `δ₀ < 1/2`;
the constant depends on `δ₀` only, never on `n`, `C`, `ε`, `δ`. -/
theorem qpac_lower_bound_log :
    ∀ δ₀ : ℝ, 0 < δ₀ → δ₀ < 1 / 2 → ∃ C₀ : ℝ, 0 < C₀ ∧
      ∀ (n : ℕ) (C : Finset (Qubits n → Bool)), IsNontrivialClass C →
        ∀ δ ε : ℝ, 0 < δ → δ ≤ δ₀ → 0 < ε → ε < 1 / 4 →
          ∀ (T : ℕ) (M : (Qubits n → Bool) →
              Matrix (Fin T → Qubits n × Bool) (Fin T → Qubits n × Bool) ℂ),
            IsQPACLearner C ε δ T M → C₀ * (Real.log (1 / δ) / ε) ≤ T := by
  sorry





end QAlgorithms.Arunachalam
