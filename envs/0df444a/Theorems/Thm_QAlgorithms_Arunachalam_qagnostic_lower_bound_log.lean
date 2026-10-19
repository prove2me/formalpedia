-- Prove2me | Theorems.Thm_QAlgorithms_Arunachalam_qagnostic_lower_bound_log
-- name    : QAlgorithms.Arunachalam.qagnostic_lower_bound_log
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-13T17:55:38.735758+00:00
-- url     : https://prove2.me/theorems/0b5f9214-a56c-4a6b-a853-f6f5fa6c72f5
-- title:
--   Quantum agnostic learners of a non-trivial class need Ω(log(1/δ)/ε²) examples
-- statement:
--   Let $C\subseteq\{c:\{0,1\}^n\to\{0,1\}\}$ be a non-trivial concept class (at least two concepts, not of the form $\{c,1-c\}$). For a distribution $D$ on $\{0,1\}^{n+1}$, the error of $h$ is $\mathrm{err}_D(h)=\Pr_{(x,b)\sim D}[h(x)\ne b]$ and $\mathrm{opt}_D(C)=\min_{c\in C}\mathrm{err}_D(c)$; a quantum example is the state $\sum_{(x,b)}\sqrt{D(x,b)}\,|x,b\rangle$. An $(\varepsilon,\delta)$-agnostic quantum learner using $T$ examples is a POVM on $T$ copies of this state with outcomes in $C$ such that, for every $D$, it outputs $h$ with $\mathrm{err}_D(h)\le\mathrm{opt}_D(C)+\varepsilon$ with probability at least $1-\delta$.
--
--   For every $\delta_0\in(0,1/2)$ there is a constant $C_0>0$ such that for all $n$, all non-trivial $C$, all $\delta\in(0,\delta_0]$, all $\varepsilon\in(0,1/4)$ and every such learner,
--
--   $$
--   T\ \ge\ C_0\,\frac{1}{\varepsilon^2}\log\frac1\delta .
--   $$
--
--   This is the concept-class-independent part of the optimal agnostic sample complexity lower bounds.
--
--   **Formalization Note** As in Lemma 7.4.1, the source's uniform constant over all $\delta\in(0,1/2)$ fails as $\delta\to1/2$; the constant here is uniform over $\delta\le\delta_0$ for each $\delta_0<1/2$.
-- source:
--   Srinivasan Arunachalam, Quantum Algorithms and Learning Theory — Part II, 2018 thesis, ILLC DS-2018-08, PDF p. 163, Lemma 7.4.2. https://ir.cwi.nl/pub/27536/Thesis_S_Arunachalam

import Definitions.Def_QAlgorithms_Defs_Learning
set_option autoImplicit false

namespace QAlgorithms.Arunachalam

open QAlgorithms.Learning



/-- Arunachalam p.163, Lemma 7.4.2: for a non-trivial concept class `C`, every
`(ε, δ)`-agnostic quantum learner for `C` with `ε ∈ (0, 1/4)` (outputting `h ∈ C` with
`err_D(h) ≤ opt_D(C) + ε` with probability `≥ 1 − δ`, for every distribution `D` on
`{0,1}^{n+1}`) uses `Ω((1/ε²) log(1/δ))` quantum examples `∑_{(x,b)} √D(x,b) |x, b⟩`.

Corrected statement (trap 30), as for Lemma 7.4.1: the constant is uniform over
`δ ∈ (0, δ₀]` for each `δ₀ < 1/2` (near `δ = 1/2` two-state discrimination needs only
`O(η²/ε²)` copies to succeed with probability `1/2 + η`). -/
theorem qagnostic_lower_bound_log :
    ∀ δ₀ : ℝ, 0 < δ₀ → δ₀ < 1 / 2 → ∃ C₀ : ℝ, 0 < C₀ ∧
      ∀ (n : ℕ) (C : Finset (Qubits n → Bool)), IsNontrivialClass C →
        ∀ δ ε : ℝ, 0 < δ → δ ≤ δ₀ → 0 < ε → ε < 1 / 4 →
          ∀ (T : ℕ) (M : {c // c ∈ C} →
              Matrix (Fin T → Qubits n × Bool) (Fin T → Qubits n × Bool) ℂ),
            IsQAgnosticLearner C ε δ T M → C₀ * (Real.log (1 / δ) / ε ^ 2) ≤ T := by
  sorry




end QAlgorithms.Arunachalam
