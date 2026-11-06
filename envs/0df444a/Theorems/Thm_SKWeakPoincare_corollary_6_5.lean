-- Prove2me | Theorems.Thm_SKWeakPoincare_corollary_6_5
-- name    : SKWeakPoincare.corollary_6_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:39:56.070243+00:00
-- url     : https://prove2.me/theorems/87a09cef-a088-4368-ae1b-06793466cf0e
-- title:
--   Corollary 6.5 — the weak Poincaré inequality along a deterministic schedule of $\le n^{C_{\mathrm{sch}}}$ temperatures
-- statement:
--   Fix $0\le\beta^*<1$ and $D,M_0,C_{\mathrm{sch}}>0$. There are constants $\Gamma>0$, depending only on $\beta^*$, and $C,a,N>0$, depending only on $(\beta^*,D,M_0,C_{\mathrm{sch}})$, such that for $n\ge N$ every deterministic set $\mathfrak B_n\subseteq[0,\beta^*]$ with $|\mathfrak B_n|\le n^{C_{\mathrm{sch}}}$ has an event of $P_{0,n}$-probability at least $1-n^{-D}$ on which
--   $$
--   \mathrm{Var}_{\mu_{\beta,A}}[f]\le Cn^a\varepsilon^{-\Gamma}\,\mathcal E_{\mu_{\beta,A}}(f,f)+\varepsilon\operatorname{osc}(f)^2
--   $$
--   for all $\beta\in\mathfrak B_n$, all $\varepsilon\in[n^{-M_0},1/2]$ and all $f:\{\pm1\}^n\to\mathbb R$.
--
--   Simulated annealing needs the inequality at every temperature of its schedule at once; this corollary provides it.
--
--   **Formalization Note** "Deterministic" means $\mathfrak B_n$ is chosen before the event, so it does not depend on $A$.
--
--   Differences from the source:
--   - encoding: a deterministic 𝔅_n ⊆ [0,β*] with |𝔅_n| ≤ n^{C_sch} → a Finset Bn of reals in [0,β*] with card ≤ n^{Csch}, quantified before the event G; reason: a deterministic set does not depend on A; |𝔅_n| ≤ n^{C_sch} forces it to be finite
--   - encoding: an event of P_{0,n}-probability at least 1 − n^{−D} → a measurable G with disorderLaw n G ≥ 1 − n^{−D}; reason: P_{0,n} is disorderLaw n
--   - encoding: 𝓔_{μ_{β,A}}(f,f) and osc(f) → glauberDirichlet (gibbs (β • W)) f and hMax f − hMin f; reason: the paper's definitions (p.2)
--   - encoding: N > 0 → N : ℕ with 0 < N; reason: n is a natural number
-- source:
--   Hou–Liu–Yu, Simulated annealing and Weak Poincaré inequalities with inverse-polynomial accuracy for the Sherrington–Kirkpatrick model, arXiv:2610.09882, Corollary 6.5, p.42

import Mathlib
import Definitions.Def_CriticalSK
import Definitions.Def_SKAnnealing_Sampling_lawMean
import Definitions.Def_SKAnnealing_Sampling_glauberKernel
import Definitions.Def_SKAnnealing_Sampling_gibbsOf

open OAI.CriticalSK SKAnnealing.Sampling MeasureTheory

namespace SKWeakPoincare

/-- **Corollary 6.5 (weak Poincaré inequality along a deterministic schedule).**
Hou–Liu–Yu, arXiv:2610.09882, Corollary 6.5, p. 42.

Fix `0 ≤ β* < 1` and `D, M₀, C_sch > 0`. There are constants `Γ > 0`, depending only on `β*`, and
`C, a, N > 0`, depending only on `(β*, D, M₀, C_sch)`, such that for `n ≥ N` every deterministic
`𝔅_n ⊆ [0, β*]` with `|𝔅_n| ≤ n^{C_sch}` has an event of `P_{0,n}`-probability at least `1 − n^{−D}`
on which `Var_{μ_{β,A}}[f] ≤ C n^a ε^{−Γ} 𝓔_{μ_{β,A}}(f, f) + ε osc(f)²` for all `β ∈ 𝔅_n`, all
`ε ∈ [n^{−M₀}, 1/2]` and all `f : {±1}^n → ℝ`.

**Formalization Note.** "Deterministic" means `𝔅_n` (a finite set of reals) is fixed before the event
`G`, i.e. does not depend on `A`. `μ_{β,A} = gibbs (β • W)`, `𝓔 = glauberDirichlet`,
`osc(f) = hMax f − hMin f`; the event is a measurable set of disorders. -/
theorem corollary_6_5 (βs : ℝ) (hβ0 : 0 ≤ βs) (hβ1 : βs < 1) :
    ∃ Γ : ℝ, 0 < Γ ∧ ∀ D M₀ Csch : ℝ, 0 < D → 0 < M₀ → 0 < Csch →
      ∃ (C a : ℝ) (N : ℕ), 0 < C ∧ 0 < a ∧ 0 < N ∧ ∀ n : ℕ, N ≤ n →
        ∀ Bn : Finset ℝ, (∀ β ∈ Bn, 0 ≤ β ∧ β ≤ βs) → (Bn.card : ℝ) ≤ (n : ℝ) ^ Csch →
          ∃ G : Set (Disorder n), MeasurableSet G ∧
            ENNReal.ofReal (1 - (n : ℝ) ^ (-D)) ≤ disorderLaw n G ∧
            ∀ W ∈ G, ∀ β ∈ Bn, ∀ ε ∈ Set.Icc ((n : ℝ) ^ (-M₀)) (1 / 2), ∀ f : Spin n → ℝ,
              lawVar (gibbs (β • W)) f ≤
                C * (n : ℝ) ^ a * ε ^ (-Γ) * glauberDirichlet (gibbs (β • W)) f +
                  ε * (hMax f - hMin f) ^ 2 := by sorry

end SKWeakPoincare
