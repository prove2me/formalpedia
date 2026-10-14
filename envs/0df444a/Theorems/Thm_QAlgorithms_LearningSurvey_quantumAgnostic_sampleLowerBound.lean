-- Prove2me | Theorems.Thm_QAlgorithms_LearningSurvey_quantumAgnostic_sampleLowerBound
-- name    : QAlgorithms.LearningSurvey.quantumAgnostic_sampleLowerBound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-13T17:55:43.850672+00:00
-- url     : https://prove2.me/theorems/99c07ccb-5b08-4358-843d-2d464c5b5e9c
-- title:
--   Quantum agnostic learning needs Ω(d/ε² + log(1/δ)/ε²) quantum examples
-- statement:
--   This is the optimal lower bound on the quantum sample complexity of agnostic learning, with the threshold on the VC dimension that the proof requires.
--
--   Let $C$ be a concept class of Boolean functions on $\{0,1\}^n$ with VC dimension $d$. For a distribution $D$ on $\{0,1\}^{n}\times\{0,1\}$ write $\mathrm{err}_D(h)=\Pr_{(x,b)\sim D}[h(x)\neq b]$ and $\mathrm{opt}_D(C)=\min_{c\in C}\mathrm{err}_D(c)$. An $(\varepsilon,\delta)$-quantum agnostic learner for $C$ with $T$ examples is a POVM $\{M_h\}_{h\in C}$ on $T$ copies of $\sum_{(x,b)}\sqrt{D(x,b)}\,|x,b\rangle$ such that for every distribution $D$ the outcome $h$ satisfies $\mathrm{err}_D(h)\le\mathrm{opt}_D(C)+\varepsilon$ with probability at least $1-\delta$.
--
--   There are an absolute constant $K>0$ and a threshold $d_0$ such that for all $n$, all $d\ge d_0$, every concept class $C$ of VC dimension $d$, all $\delta\in(0,1/2)$ and $\varepsilon\in(0,1/10)$, every $(\varepsilon,\delta)$-quantum agnostic learner for $C$ uses
--
--   $$
--   T\ \ge\ K\Big(\frac{d}{\varepsilon^2}+\frac{1}{\varepsilon^2}\log\frac{1}{\delta}\Big)
--   $$
--
--   examples.
--
--   It shows that quantum examples give no advantage for agnostic learning either: the bound matches the classical sample complexity up to constants.
--
--   **Formalization Note** The source prints the bound for every $d$; it is false at $d=0$ (one concept, no examples needed) and at small $d$ with $\delta$ close to $1/2$ (for $C=\{c,\neg c\}$ one example measured in the computational basis is an $(\varepsilon,1/2-\varepsilon/2)$-learner). The threshold $d_0$ is the source's "sufficiently large constant" from the code argument. The learner is proper: its outcomes are the concepts of $C$.
-- source:
--   Srinivasan Arunachalam and Ronald de Wolf, A Survey of Quantum Learning Theory, 2017, v3, PDF p. 14, Theorem 4.15. https://arxiv.org/pdf/1701.06806v3

import Definitions.Def_QAlgorithms_Defs_LearningHardInstances
set_option autoImplicit false

namespace QAlgorithms.LearningSurvey

open MeasureTheory QAlgorithms.Learning



/-- survey p.14, Theorem 4.15 ([AW17]): optimal quantum agnostic sample-complexity lower bound.
Let `C` be a concept class on `{0,1}^n` with VC dimension `d`. For every `δ ∈ (0, 1/2)` and
`ε ∈ (0, 1/10)`, every `(ε, δ)`-quantum agnostic learner for `C` (a POVM on `T` copies of
`Σ_{(x,b)} √D(x,b) |x, b⟩` whose outcomes are concepts of `C`, outputting with probability
`≥ 1 − δ` an `h ∈ C` with `err_D(h) ≤ opt_D(C) + ε`, for every distribution `D`) uses
`T = Ω(d/ε² + (1/ε²) log(1/δ))` copies.

Corrected statement (trap 30): the `Ω` carries a threshold `d₀` on `d` (the source's proof needs
the linear code of p.14, which exists for `d` a sufficiently large constant). Without it the
printed statement is false: at `d = 0` the class has at most one concept and `T = 0` suffices; at
`d = 1`, for `C = {c, ¬c}`, one copy measured in the computational basis (output `c` iff the label
agrees with `c`) is an `(ε, 1/2 − ε/2)`-learner, while `K/ε² → ∞` as `ε → 0`. -/
theorem quantumAgnostic_sampleLowerBound :
    ∃ K : ℝ, 0 < K ∧ ∃ d₀ : ℕ, ∀ (n d : ℕ) (C : Finset (Qubits n → Bool)), d₀ ≤ d →
      vcDimClass C = d →
      ∀ δ ε : ℝ, 0 < δ → δ < 1 / 2 → 0 < ε → ε < 1 / 10 →
      ∀ (T : ℕ) (M : {c // c ∈ C} →
          Matrix (Fin T → Qubits n × Bool) (Fin T → Qubits n × Bool) ℂ),
        IsQAgnosticLearner C ε δ T M →
        K * ((d : ℝ) / ε ^ 2 + (1 / ε ^ 2) * Real.log (1 / δ)) ≤ (T : ℝ) := by sorry


end QAlgorithms.LearningSurvey
