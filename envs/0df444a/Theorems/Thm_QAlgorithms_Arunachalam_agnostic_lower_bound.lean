-- Prove2me | Theorems.Thm_QAlgorithms_Arunachalam_agnostic_lower_bound
-- name    : QAlgorithms.Arunachalam.agnostic_lower_bound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-13T17:55:55.17498+00:00
-- url     : https://prove2.me/theorems/6471c94c-4503-4653-b0c3-1d3c0d489a1c
-- title:
--   Classical agnostic sample complexity is Ω(d/ε² + log(1/δ)/ε²)
-- statement:
--   Let $C\subseteq\{c:\{0,1\}^n\to\{0,1\}\}$ be a concept class of VC dimension $d\ge1$. For a distribution $D$ on $\{0,1\}^{n+1}$ let $\mathrm{err}_D(h)=\Pr_{(x,b)\sim D}[h(x)\ne b]$ and $\mathrm{opt}_D(C)=\min_{c\in C}\mathrm{err}_D(c)$. A classical $(\varepsilon,\delta)$-agnostic learner using $T$ samples is a randomized map from $T$ i.i.d. samples $(x_i,b_i)\sim D$ to hypotheses in $C$ such that, for every $D$, it outputs $h$ with $\mathrm{err}_D(h)\le\mathrm{opt}_D(C)+\varepsilon$ with probability at least $1-\delta$.
--
--   For every $\delta_0\in(0,1/2)$ there is a constant $C_0>0$ such that for all $n$, $d\ge1$, all $C$ of VC dimension $d$, all $\delta\in(0,\delta_0]$, all $\varepsilon\in(0,1/4)$ and every such learner,
--
--   $$
--   T\ \ge\ C_0\left(\frac d{\varepsilon^2}+\frac{\log(1/\delta)}{\varepsilon^2}\right).
--   $$
--
--   Together with the matching upper bound this pins down the classical agnostic sample complexity up to constant factors.
--
--   **Formalization Note** Two corrections of the source: the constant is uniform over $\delta\le\delta_0<1/2$ (as in Lemma 7.4.2), and $d\ge1$ is assumed, since at $d=0$ the class has at most one concept and outputting it without samples is an agnostic learner.
-- source:
--   Srinivasan Arunachalam, Quantum Algorithms and Learning Theory — Part II, 2018 thesis, ILLC DS-2018-08, PDF p. 165, Theorem 7.4.4. https://ir.cwi.nl/pub/27536/Thesis_S_Arunachalam

import Definitions.Def_QAlgorithms_Defs_Learning
set_option autoImplicit false

namespace QAlgorithms.Arunachalam

open QAlgorithms.Learning





/-- Arunachalam p.165–166, Theorem 7.4.4: for a concept class `C` with `VC-dim(C) = d`, every
(randomized) classical `(ε, δ)`-agnostic learner for `C` with `ε ∈ (0, 1/4)` (outputting
`h ∈ C` with `err_D(h) ≤ opt_D(C) + ε` with probability `≥ 1 − δ`, for every distribution `D` on
`{0,1}^{n+1}`) uses `Ω(d/ε² + log(1/δ)/ε²)` samples.

Corrected statement (trap 30): the constant is uniform over `δ ∈ (0, δ₀]` for each
`δ₀ < 1/2` (as Lemma 7.4.2); and `d ≥ 1` is assumed (at `d = 0` the class has at most one
concept, and outputting it without samples is an `(ε, δ)`-agnostic learner). -/
theorem agnostic_lower_bound :
    ∀ δ₀ : ℝ, 0 < δ₀ → δ₀ < 1 / 2 → ∃ C₀ : ℝ, 0 < C₀ ∧
      ∀ (n : ℕ) (C : Finset (Qubits n → Bool)) (d : ℕ), vcDimClass C = d → 1 ≤ d →
        ∀ δ ε : ℝ, 0 < δ → δ ≤ δ₀ → 0 < ε → ε < 1 / 4 →
          ∀ (T : ℕ) (L : (Fin T → Qubits n × Bool) → PMF (Qubits n → Bool)),
            IsAgnosticLearner C ε δ T L →
              C₀ * ((d : ℝ) / ε ^ 2 + Real.log (1 / δ) / ε ^ 2) ≤ T := by
  sorry


end QAlgorithms.Arunachalam
