-- Prove2me | Theorems.Thm_ReusableAssort_Hybrid_epsStar_isBigO
-- name    : ReusableAssort.Hybrid.epsStar_isBigO
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T17:27:46.863851+00:00
-- url     : https://prove2.me/theorems/4de86d16-dda8-4ccf-b9ec-c1980890bb23
-- title:
--   §3, p. 11 — ε*(x) and every minimizer γ*(x) are O(√(log x / x))
-- statement:
--   Let $\varepsilon^*(x) = \min_{\gamma \in [0,1]} 1 - (1-\gamma)\big(1 - \exp(-\gamma^2 x/(2-\gamma))\big)$ as in (1). There are constants $C > 0$ and $x_0$ such that for every real $x \ge x_0$,
--   $$\varepsilon^*(x) \le C \sqrt{\frac{\log x}{x}} \qquad\text{and}\qquad \gamma \le C\sqrt{\frac{\log x}{x}} \ \text{ for every minimizer } \gamma = \gamma^*(x).$$
--
--   This quantifies how fast the guarantee $1 - \varepsilon^*(c_{\min})$ of Theorem 1 approaches $1$.
--
--   **Formalization Note** The constants are chosen before $x$, so they are absolute. The page states the claim for $x = c_{\min}$; it is stated here for all real $x \ge x_0$.
-- source:
--   Feng, Niazadeh & Saberi, arXiv:2512.06997v1, p. 11, §3 (sentence after eq. (1))

import Mathlib
import Definitions.Def_ReusableAssort_Hybrid_Model

namespace ReusableAssort.Hybrid

theorem epsStar_isBigO :
    ∃ C x₀ : ℝ, 0 < C ∧ ∀ x ≥ x₀,
      epsStar x ≤ C * Real.sqrt (Real.log x / x) ∧
      ∀ γ, IsGammaStar x γ → γ ≤ C * Real.sqrt (Real.log x / x) := by sorry

end ReusableAssort.Hybrid
