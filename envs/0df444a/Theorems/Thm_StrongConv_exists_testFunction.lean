-- Prove2me | Theorems.Thm_StrongConv_exists_testFunction
-- name    : StrongConv.exists_testFunction
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-04T22:42:07.924729+00:00
-- url     : https://prove2.me/theorems/4e0bdc5b-ff62-480b-8d08-a83f7f789abe
-- title:
--   Lemma 4.10 — smooth test functions with controlled derivatives
-- statement:
--   There is a universal constant $C$ such that for every integer $m \ge 1$ and all $K, \rho, \varepsilon > 0$ with $\rho + \varepsilon < K$ there is a smooth $\chi : \mathbb R \to \mathbb R$ with $0 \le \chi \le 1$, $\chi(x) = 0$ for $|x| \le \rho + \frac\varepsilon2$, $\chi(x) = 1$ for $|x| \ge \rho + \varepsilon$, and, with $f(\theta) = \chi(K\cos\theta)$,
--   $$\|f^{(m+1)}\|_{L^\beta[0,2\pi]} \le (Cm)^m \Big(\frac K\varepsilon\Big)^{m + 1/\beta_*} \quad \text{for every } \beta > 1, \qquad \frac1{\beta_*} = 1 - \frac1\beta.$$
-- source:
--   Chen, C.-F., Garza-Vargas, J., Tropp, J. A. and van Handel, R., A new approach to strong convergence, Ann. of Math. (2) 203 (2026) 555–602, https://doi.org/10.4007/annals.2026.203.2.4 (arXiv:2405.16026v3, whose page numbers are used), pp. 18–19, Lemma 4.10 (test functions)

import Mathlib
import Definitions.Def_StrongConv

namespace StrongConv

theorem exists_testFunction :
    ∃ C : ℝ, ∀ (m : ℕ) (K ρ ε : ℝ), 1 ≤ m → 0 < K → 0 < ρ → 0 < ε → ρ + ε < K →
      ∃ χ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ ∧ (∀ x, χ x ∈ Set.Icc 0 1) ∧
        (∀ x, |x| ≤ ρ + ε / 2 → χ x = 0) ∧ (∀ x, ρ + ε ≤ |x| → χ x = 1) ∧
        ∀ β : ℝ, 1 < β →
          lpNormCircle β (iteratedDeriv (m + 1) (fun θ => χ (K * Real.cos θ))) ≤
            (C * m) ^ m * (K / ε) ^ ((m : ℝ) + 1 / conjExp β) := by
  sorry

end StrongConv
