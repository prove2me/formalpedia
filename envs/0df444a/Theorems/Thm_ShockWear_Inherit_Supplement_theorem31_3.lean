-- Prove2me | Theorems.Thm_ShockWear_Inherit_Supplement_theorem31_3
-- name    : ShockWear.Inherit.Supplement.theorem31_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T23:57:34.698256+00:00
-- url     : https://prove2.me/theorems/465074c8-8f25-42c9-b2f0-0f6b37fe992f
-- title:
--   Theorem 3.1(3.3) — decreasing normalized tail sums of shock survival probabilities give DMRL
-- statement:
--   Let shocks arrive at rate $\lambda>0$, let $1=\bar P_0\geq\bar P_1\geq\cdots\geq0$ be the probabilities of surviving the first $k$ shocks, and let $\bar H$ be the Poisson shock survival function (2.1). Suppose that the normalized tail sums
--   $$k\longmapsto\frac{\sum_{j=k}^\infty\bar P_j}{\bar P_k}$$
--   are decreasing in $k=0,1,\dots$ (over the indices with $\bar P_k>0$). Then $H$ has decreasing mean residual life: the mean residual life
--   $$t\longmapsto\frac{\int_0^\infty\bar H(x+t)\,dx}{\bar H(t)}$$
--   is decreasing in $t$ wherever $\bar H(t)>0$.
--
--   The discrete hypothesis is the analogue, for the number of shocks survived, of the continuous DMRL property it yields.
--
--   **Formalization Note** "Decreasing" is weak. The tail sums and the integral are computed in $[0,\infty]$ (they are infinite when $\sum_j\bar P_j=\infty$), and both ratios are taken only where the denominator is positive, as the paper's convention of avoiding zero denominators requires. The DMRL property is stated on every real $t$ with $\bar H(t)>0$, with $\bar H=1$ on $t<0$ as in (2.1). Nonnegativity and weak monotonicity of the $\bar P_k$ are the paper's standing assumption (2.2).
-- source:
--   Esary, Marshall and Proschan, Shock Models and Wear Processes, Ann. Probability 1 (1973), p. 632, Theorem 3.1 (3.3), with definition (iii), p. 631; https://doi.org/10.1214/aop/1176996891

import Mathlib
import Definitions.Def_ShockWear_Inherit_Model

namespace ShockWear.Inherit.Supplement

open scoped ENNReal

/-- Theorem 3.1(3.3): decreasing normalized tail sums of the shock survival
probabilities give a DMRL life law. -/
theorem theorem31_3 (lam : ℝ) (hlam : 0 < lam) (P : ℕ → ℝ)
    (hP0 : P 0 = 1) (hanti : Antitone P) (hnn : ∀ k, 0 ≤ P k)
    (htail : AntitoneOn
      (fun k => (∑' j, ENNReal.ofReal (P (j + k))) / ENNReal.ofReal (P k))
      {k | 0 < P k}) :
    IsDMRL (ShockWear.CumDamage.shockSurv lam P) := by sorry

end ShockWear.Inherit.Supplement
