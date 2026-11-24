-- Prove2me | Theorems.Thm_ShockWear_Inherit_Supplement_theorem31_6
-- name    : ShockWear.Inherit.Supplement.theorem31_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T23:58:23.982844+00:00
-- url     : https://prove2.me/theorems/1a87c1df-bfd6-4e5e-afad-8243eccb4586
-- title:
--   Theorem 3.1(3.6) — the discrete NBUE condition on shock survival probabilities gives NBUE
-- statement:
--   Let shocks arrive at rate $\lambda>0$, let $1=\bar P_0\geq\bar P_1\geq\cdots\geq0$ be the probabilities of surviving the first $k$ shocks, and let $\bar H$ be the Poisson shock survival function (2.1). Suppose that
--   $$\bar P_k\sum_{j=0}^\infty\bar P_j\;\geq\;\sum_{j=k}^\infty\bar P_j,\qquad k=0,1,\dots.$$
--   Then $H$ is new better than used in expectation: for every $t\geq0$ with $\bar H(t)>0$,
--   $$\int_0^\infty\bar H(x)\,dx\;\geq\;\frac{\int_0^\infty\bar H(t+x)\,dx}{\bar H(t)}.$$
--
--   The mean life of a new item is at least the mean residual life of an item that has survived to any age $t$.
--
--   **Formalization Note** Sums and integrals are computed in $[0,\infty]$, with $0\cdot\infty=0$; when $\sum_j\bar P_j=\infty$ both sides of the conclusion are infinite. The ratio is taken only where $\bar H(t)>0$. Nonnegativity and weak monotonicity of the $\bar P_k$ are the paper's standing assumption (2.2).
-- source:
--   Esary, Marshall and Proschan, Shock Models and Wear Processes, Ann. Probability 1 (1973), p. 632, Theorem 3.1 (3.6), with definition (vi), p. 631; https://doi.org/10.1214/aop/1176996891

import Mathlib
import Definitions.Def_ShockWear_Inherit_Model

namespace ShockWear.Inherit.Supplement

open scoped ENNReal

/-- Theorem 3.1(3.6): the discrete NBUE condition on the shock survival
probabilities gives an NBUE life law. -/
theorem theorem31_6 (lam : ℝ) (hlam : 0 < lam) (P : ℕ → ℝ)
    (hP0 : P 0 = 1) (hanti : Antitone P) (hnn : ∀ k, 0 ≤ P k)
    (hnbue : ∀ k, ∑' j, ENNReal.ofReal (P (j + k)) ≤
      ENNReal.ofReal (P k) * ∑' j, ENNReal.ofReal (P j)) :
    IsNBUE (ShockWear.CumDamage.shockSurv lam P) := by sorry

end ShockWear.Inherit.Supplement
