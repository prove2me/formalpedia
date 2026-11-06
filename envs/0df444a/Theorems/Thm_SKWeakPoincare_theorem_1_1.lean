-- Prove2me | Theorems.Thm_SKWeakPoincare_theorem_1_1
-- name    : SKWeakPoincare.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:39:43.909001+00:00
-- url     : https://prove2.me/theorems/414b9509-faa9-4302-a05e-d88dae325d1d
-- title:
--   Theorem 1.1 — polynomial-scale weak Poincaré inequality for the SK model at every $\beta<1$
-- statement:
--   Fix $0\le\beta<1$ and $D,M_0>0$. There are constants $\Gamma>0$, depending only on $\beta$, and $C,B,N>0$, depending only on $(\beta,D,M_0)$, such that for $n\ge N$, with $P_{0,n}$-probability at least $1-n^{-D}$,
--   $$
--   \mathrm{Var}_{\mu_A}[f]\le Cn^{7+B\Gamma}\varepsilon^{-\Gamma}\,\mathcal E_{\mu_A}(f,f)+\varepsilon\operatorname{osc}(f)^2
--   $$
--   simultaneously for every $\varepsilon\in[n^{-M_0},1/2]$ and every $f:\{\pm1\}^n\to\mathbb R$.
--
--   Here $A\sim P_{0,n}$ is the SK interaction matrix, $\mu_A=\mu_{\beta,A}$ is the Gibbs measure, $\mathcal E_{\mu_A}(f,f)=\frac1n\sum_{i=1}^nE_{X\sim\mu_A}\big[\mathrm{Var}_{X\sim\mu_A}[f(X)\mid X_{-i}]\big]$ is the Glauber Dirichlet form and $\operatorname{osc}(f)=\max f-\min f$. A weak Poincaré inequality with polynomial constants at inverse-polynomial accuracy $\varepsilon$ is what simulated annealing needs.
--
--   **Formalization Note** The event is a measurable set $G$ of disorders, chosen before $\varepsilon$ and $f$.
--
--   Differences from the source:
--   - encoding: with P_{0,n}-probability at least 1 − n^{−D}, simultaneously for every ε and f → ∃ measurable G with disorderLaw n G ≥ 1 − n^{−D}, and the inequality for every W ∈ G, ε and f; reason: P_{0,n} is disorderLaw n; G is chosen before ε and f
--   - encoding: 𝓔_{μ_A}(f,f) and osc(f) → glauberDirichlet (gibbs (β • W)) f and hMax f − hMin f; reason: Pᵢf is the conditional expectation given X₋ᵢ, so E_μ[(f − Pᵢf)²] = E_μ[Var(f | X₋ᵢ)]
--   - encoding: N > 0 → N : ℕ with 0 < N; reason: n is a natural number
-- source:
--   Hou–Liu–Yu, Simulated annealing and Weak Poincaré inequalities with inverse-polynomial accuracy for the Sherrington–Kirkpatrick model, arXiv:2610.09882, Theorem 1.1, pp.2–3

import Mathlib
import Definitions.Def_CriticalSK
import Definitions.Def_SKAnnealing_Sampling_lawMean
import Definitions.Def_SKAnnealing_Sampling_glauberKernel
import Definitions.Def_SKAnnealing_Sampling_gibbsOf

open OAI.CriticalSK SKAnnealing.Sampling MeasureTheory

namespace SKWeakPoincare

/-- **Theorem 1.1 (polynomial-scale weak Poincaré inequality).**
Hou–Liu–Yu, arXiv:2610.09882, Theorem 1.1, pp. 2–3.

Fix `0 ≤ β < 1` and `D, M₀ > 0`. There are constants `Γ > 0`, depending only on `β`, and
`C, B, N > 0`, depending only on `(β, D, M₀)`, such that for `n ≥ N`, with `P_{0,n}`-probability at
least `1 − n^{−D}`,
`Var_{μ_A}[f] ≤ C n^{7+BΓ} ε^{−Γ} 𝓔_{μ_A}(f, f) + ε osc(f)²`
simultaneously for every `ε ∈ [n^{−M₀}, 1/2]` and every `f : {±1}^n → ℝ`.

**Formalization Note.** `A` is `W : Disorder n` with law `disorderLaw n = P_{0,n}`; `μ_A = gibbs (β • W)`;
`𝓔_{μ_A}(f, f) = n⁻¹ Σᵢ E[Var(f(X) | X₋ᵢ)]` is `glauberDirichlet`; `osc(f) = hMax f − hMin f`. The event
is a measurable set `G` with `disorderLaw n G ≥ 1 − n^{−D}`, chosen before `ε` and `f`. Powers are real
powers of `(n : ℝ)` and `ε`. -/
theorem theorem_1_1 (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    ∃ Γ : ℝ, 0 < Γ ∧ ∀ D M₀ : ℝ, 0 < D → 0 < M₀ →
      ∃ (C B : ℝ) (N : ℕ), 0 < C ∧ 0 < B ∧ 0 < N ∧ ∀ n : ℕ, N ≤ n →
        ∃ G : Set (Disorder n), MeasurableSet G ∧
          ENNReal.ofReal (1 - (n : ℝ) ^ (-D)) ≤ disorderLaw n G ∧
          ∀ W ∈ G, ∀ ε ∈ Set.Icc ((n : ℝ) ^ (-M₀)) (1 / 2), ∀ f : Spin n → ℝ,
            lawVar (gibbs (β • W)) f ≤
              C * (n : ℝ) ^ (7 + B * Γ) * ε ^ (-Γ) * glauberDirichlet (gibbs (β • W)) f +
                ε * (hMax f - hMin f) ^ 2 := by sorry

end SKWeakPoincare
