-- Prove2me | Theorems.Thm_SampleDrivenOS_Linear_b9_c_le
-- name    : SampleDrivenOS.Linear.b9_c_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:01:20.458504+00:00
-- url     : https://prove2.me/theorems/1de6281f-0fb6-4cae-84fd-430e42db324e
-- title:
--   B.9, p. 37 — $c(p)\le 1/p-\alpha^*(1-p)(1+1/p)$
-- statement:
--   Let $\alpha^*\in(0,1)$ satisfy $\int_0^1 dy/(y(1-\ln y)+1/\alpha^*-1)=1$, and suppose $\alpha^*\in[0.74,\,0.75]$. Then for every $p\in(0,1)$,
--   $$c(p)\le\frac1p-\alpha^*(1-p)\Bigl(1+\frac1p\Bigr),\qquad c(p)=\sum_{i=1}^{\infty}\frac{p^{i-1}-p^i}{\tfrac1{p\alpha^*}-1+p^i(1+i(1-p))}.$$
--
--   This is the upper bound on $c$ that, with $b(p)\ge 1/p$, gives $a'(p)\le 0$.
--
--   **Formalization Note** The paper prints "$c(p)\ge\dots$"; this is a slip: the sentence concludes the estimate announced as "We now show that $c(p)\le 1/p-\alpha^*(1-p)-\alpha^*\frac{1-p}{p}$" (p. 36), and it is used as an upper bound in the next display. The formal statement uses $\le$. The paper uses "$\alpha^*\approx 0.745$" through the interval $[0.74,0.75]$ of the preceding numerical check; that interval is a hypothesis here. Its lower half is implied by the separately posed `CorreaThreshold.Adaptive.inv_beta_star_gt` ($\alpha^*>0.745$); the upper half $\alpha^*\le 0.75$ is numerically true ($\alpha^*\approx 0.74544$) and posed nowhere. The series is a Lean `tsum` with the index shifted by one.
-- source:
--   Correa, Cristi, Epstein & Soto, Sample-Driven Optimal Stopping: From the Secretary Problem to the i.i.d. Prophet Inequality, arXiv:2011.06516v2, p. 37, B.9 (Proof of Theorem 9), sentence before the last display (printed with ≥, a slip for ≤)

import Mathlib
import Definitions.Def_SampleDrivenOS_Linear_Setting

namespace SampleDrivenOS.Linear

theorem b9_c_le (s : ℝ) (hs : SampleDrivenOS.Limit.IsAlphaStar s) (hs' : s ∈ Set.Icc (0.74 : ℝ) 0.75) (p : ℝ)
    (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    cB9 s p ≤ 1 / p - s * (1 - p) * (1 + 1 / p) := by sorry

end SampleDrivenOS.Linear
