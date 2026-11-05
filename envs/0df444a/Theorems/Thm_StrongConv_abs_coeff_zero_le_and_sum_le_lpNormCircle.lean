-- Prove2me | Theorems.Thm_StrongConv_abs_coeff_zero_le_and_sum_le_lpNormCircle
-- name    : StrongConv.abs_coeff_zero_le_and_sum_le_lpNormCircle
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-04T22:40:13.476655+00:00
-- url     : https://prove2.me/theorems/3d879b7b-a171-4b70-b7d1-1453c21c803e
-- title:
--   Lemma 4.4 — Zygmund's bound on Chebyshev coefficients
-- statement:
--   There is a universal constant $C$ with the following property. Let $K > 0$, let $a_0, a_1, \dots, a_q$ be real, and put $h(x) = \sum_{j=0}^q a_j T_j(x/K)$, where $T_j$ is the Chebyshev polynomial of the first kind, and $f(\theta) = h(K\cos\theta)$. Then $|a_0| \le \sup_{x \in [-K, K]} |h(x)|$, and for every $m \ge 0$ and $\beta > 1$,
--   $$\sum_{j=1}^q j^m |a_j| \le C\,\beta_*\,\|f^{(m+1)}\|_{L^\beta[0, 2\pi]}, \qquad \frac1{\beta_*} = 1 - \frac1\beta.$$
--   The paper's $\lesssim$ is read as a universal constant, independent of $q$, $K$, $m$ and $\beta$.
-- source:
--   Chen, C.-F., Garza-Vargas, J., Tropp, J. A. and van Handel, R., A new approach to strong convergence, Ann. of Math. (2) 203 (2026) 555–602, https://doi.org/10.4007/annals.2026.203.2.4 (arXiv:2405.16026v3, whose page numbers are used), pp. 16–17, Lemma 4.4 (Zygmund), which applies Zygmund, A., Trigonometric series, Vols. I–II, third edition, Cambridge University Press (2002), p. 242, https://doi.org/10.1017/CBO9781316036587

import Mathlib
import Definitions.Def_StrongConv

open Polynomial

namespace StrongConv

theorem abs_coeff_zero_le_and_sum_le_lpNormCircle :
    ∃ C : ℝ, ∀ (q : ℕ) (a : ℕ → ℝ) (K : ℝ), 0 < K →
      |a 0| ≤ cNorm 0 (fun x => ∑ j ∈ Finset.range (q + 1),
          a j * (Chebyshev.T ℝ j).eval (x / K)) (-K) K ∧
      ∀ (m : ℕ) (β : ℝ), 1 < β →
        ∑ j ∈ Finset.Icc 1 q, (j : ℝ) ^ m * |a j| ≤
          C * conjExp β * lpNormCircle β (iteratedDeriv (m + 1) (fun θ =>
            ∑ j ∈ Finset.range (q + 1), a j * (Chebyshev.T ℝ j).eval (K * Real.cos θ / K))) := by
  sorry

end StrongConv
