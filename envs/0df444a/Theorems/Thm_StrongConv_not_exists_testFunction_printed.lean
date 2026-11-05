-- Prove2me | Theorems.Thm_StrongConv_not_exists_testFunction_printed
-- name    : StrongConv.not_exists_testFunction_printed
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-04T23:13:47.371904+00:00
-- url     : https://prove2.me/theorems/5c78158e-a116-4e17-bd3c-4a54973854ba
-- title:
--   Chen–Garza-Vargas–Tropp–van Handel, Lemma 4.10 at m = 0 is false
-- statement:
--   There is no constant $C$ such that for every integer $m \ge 0$ and all $K, \rho, \varepsilon > 0$ with $\rho + \varepsilon < K$ there is a smooth $\chi : \mathbb R \to \mathbb R$ with $0 \le \chi \le 1$, $\chi(x) = 0$ for $|x| \le \rho + \frac\varepsilon2$, $\chi(x) = 1$ for $|x| \ge \rho + \varepsilon$, and
--   $$\|f^{(m+1)}\|_{L^\beta[0,2\pi]} \le (Cm)^m\Big(\frac K\varepsilon\Big)^{m + 1/\beta_*} \quad \text{for every } \beta > 1,$$
--   where $f(\theta) = \chi(K\cos\theta)$, $1/\beta_* = 1 - 1/\beta$, and $(Cm)^m = 1$ at $m = 0$.
--
--   This is Lemma 4.10 of C.-F. Chen, J. Garza-Vargas, J. A. Tropp and R. van Handel, *A new approach to strong convergence*, Ann. of Math. (2) 203 (2026) 555–602 (arXiv v3, p. 18), over its printed range $m \in \mathbb Z_+ = \{0, 1, 2, \dots\}$ (p. 3): “*Fix $m \in \mathbb Z_+$ and $K, \rho, \varepsilon > 0$ so that $\rho + \varepsilon < K$. Then there exists a function $\chi \in C^\infty(\mathbb R)$ with the following properties.*” At $m = 0$ the bound reads $\|f'\|_{L^\beta} \le (K/\varepsilon)^{1/\beta_*}$, which fails for every admissible $\chi$ once $\rho + \varepsilon \ll K$: $f$ rises from $0$ to $1$ across each of four $\theta$-intervals of length about $\frac{\varepsilon}{2K}$. The mission states the lemma for $m \ge 1$ (`StrongConv.exists_testFunction`); every application in the paper takes $m \ge 4$.
-- source:
--   Chen, C.-F., Garza-Vargas, J., Tropp, J. A. and van Handel, R., A new approach to strong convergence, Ann. of Math. (2) 203 (2026) 555–602, https://doi.org/10.4007/annals.2026.203.2.4 (arXiv:2405.16026v3, whose page numbers are used), p. 18, Lemma 4.10 at m = 0 (printed-fails lemma, not in the paper)

import Mathlib
import Definitions.Def_StrongConv

open Filter Topology Polynomial

namespace StrongConv

theorem not_exists_testFunction_printed :
    ¬ ∃ C : ℝ, ∀ (m : ℕ) (K ρ ε : ℝ), 0 < K → 0 < ρ → 0 < ε → ρ + ε < K →
      ∃ χ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ ∧ (∀ x, χ x ∈ Set.Icc 0 1) ∧
        (∀ x, |x| ≤ ρ + ε / 2 → χ x = 0) ∧ (∀ x, ρ + ε ≤ |x| → χ x = 1) ∧
        ∀ β : ℝ, 1 < β →
          lpNormCircle β (iteratedDeriv (m + 1) (fun θ => χ (K * Real.cos θ))) ≤
            (C * m) ^ m * (K / ε) ^ ((m : ℝ) + 1 / conjExp β) := by
  sorry

end StrongConv
