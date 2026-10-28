-- Prove2me | Theorems.Thm_SluggishCapability_Myopic_two_state_feasible
-- name    : SluggishCapability.Myopic.two_state_feasible
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T23:05:46.696371+00:00
-- url     : https://prove2.me/theorems/b01c0592-7b95-4419-bcab-d14623fcde1d
-- title:
--   §3, p. 11 — the two-state program has invariant law (β, 1)/(1 + β) and average intensity 2µ/(1 + β) ≤ µ + ε for β near 1
-- statement:
--   Let $\mu \ge 0$ be an integer. For $0 < \beta \le 1$ consider the two-state program with states $L, H$,
--   $$P = \begin{pmatrix} 0 & 1 \\ \beta & 1-\beta \end{pmatrix} \ (\text{rows and columns } L, H), \qquad f(L) = 0,\ f(H) = 2\mu .$$
--   Then
--
--   1. $P$ is stochastic and irreducible;
--   2. $(\lambda(L), \lambda(H)) = \left(\frac{\beta}{1+\beta}, \frac{1}{1+\beta}\right)$ is invariant for $P$;
--   3. the long-run average intensity is $\sum_s \lambda(s) f(s) = \dfrac{2\mu}{1+\beta}$;
--   4. for every $\varepsilon > 0$ there is $\beta_0 \in [0, 1)$ such that $\dfrac{2\mu}{1+\beta} \le \mu + \varepsilon$ for all $\beta \in (\beta_0, 1)$.
--
--   Together these say the program of Proposition 1(ii) satisfies the intensity constraint (1) when $\beta$ is close enough to $1$.
--
--   **Formalization Note** Index `0` is $L$ and index `1` is $H$.
-- source:
--   Eliaz, Spiegler, Capability Building in Sluggish Organizations, authors' manuscript of March 28, 2022 (Management Science 2023, doi:10.1287/mnsc.2022.4445), p. 11, remark after Proposition 1 (long-run average intensity 2µ/(1 + β))

import Mathlib
import Definitions.Def_mm_basic
import Definitions.Def_SluggishCapability_Myopic_Setting

open MarkovMixing

namespace SluggishCapability.Myopic

/-- §3, p. 11: for `β ∈ (0, 1]` the two-state program (index `0` is `L`, `1` is `H`) is stochastic
and irreducible, its invariant distribution is `(λ(L), λ(H)) = (β/(1 + β), 1/(1 + β))`, and its
long-run average intensity is `2µ/(1 + β)`; for every `ε > 0` this is at most `µ + ε` for all `β`
sufficiently close to `1`. -/
theorem two_state_feasible (μ : ℕ) :
    (∀ β : ℝ, 0 < β → β ≤ 1 →
      IsStochastic (twoStateP β) ∧ MarkovMixing.Irreducible (twoStateP β) ∧
      IsStationary (twoStateP β) ![β / (1 + β), 1 / (1 + β)] ∧
      ∑ s : Fin 2, ![β / (1 + β), 1 / (1 + β)] s * (twoStateF μ s : ℝ) =
        2 * (μ : ℝ) / (1 + β)) ∧
    ∀ ε : ℝ, 0 < ε → ∃ β₀ : ℝ, 0 ≤ β₀ ∧ β₀ < 1 ∧
      ∀ β : ℝ, β₀ < β → β < 1 → 2 * (μ : ℝ) / (1 + β) ≤ (μ : ℝ) + ε := by sorry

end SluggishCapability.Myopic
