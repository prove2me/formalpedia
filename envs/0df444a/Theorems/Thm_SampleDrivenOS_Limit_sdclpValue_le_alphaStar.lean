-- Prove2me | Theorems.Thm_SampleDrivenOS_Limit_sdclpValue_le_alphaStar
-- name    : SampleDrivenOS.Limit.sdclpValue_le_alphaStar
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-10-23T17:45:08.165609+00:00
-- url     : https://prove2.me/theorems/94cbea99-b7ba-4510-8cb7-51047252c1f0
-- title:
--   Theorem 8 (upper half) — $\alpha(p)\le\alpha^*$: the SDCLP$_p$ value is at most the i.i.d. prophet constant
-- statement:
--   Let $p\in(0,1)$ and let $\alpha^*\in(0,1)$ be a solution of
--   $$\int_0^1\frac{dy}{y(1-\ln y)+1/\alpha^*-1}=1$$
--   (the i.i.d. prophet constant, $\alpha^*\approx 0.745$). Let $\alpha(p)$ be the optimal value of the continuous linear program SDCLP$_p$:
--   $$\alpha(p)=\sup\Big\{\alpha\in[0,1]\;:\;\exists\, q\ge 0,\ \ t\,q(t,\ell)+\int_p^t\sum_{s\ge1}q(\tau,s)\,d\tau\le 1\ \ \forall t\in[p,1],\ \ell\ge1,\ \ \alpha\le \frac{F_k(q)}{1-p^k}\ \ \forall k\ge1\Big\},$$
--   where $F_k(q)=\sum_{\ell=1}^k\int_p^1 q(t,\ell)\sum_{j=\ell}^k\binom{j-1}{\ell-1}(1-t)^{j-\ell}t^\ell\,dt$. Then
--   $$\alpha(p)\le\alpha^* .$$
--
--   This is the upper-bound half of the chain $0\le\tilde\alpha(p)\le\alpha(p)\le\alpha^*$ in Theorem 8. In the paper it is not derived from the program itself: $\alpha(p)$ is the optimal competitive ratio of the sample-driven optimal stopping problem $p$-DOS (as $N\to\infty$), and $\alpha^*$ is the optimal factor of the i.i.d. prophet inequality with full distributional knowledge, a more informed setting, so $\alpha(p)\le\alpha^*$ (the paper cites Kaplan et al., Theorem 3.4, for this comparison). A proof directly about SDCLP$_p$ has to reproduce that argument, e.g. by exhibiting weights on the constraints (11) that certify the bound.
-- source:
--   Correa, Cristi, Epstein & Soto, Sample-Driven Optimal Stopping: From the Secretary Problem to the i.i.d. Prophet Inequality, arXiv:2011.06516v2, p. 17, Theorem 8 (the inequality α(p) ≤ α*), and its proof in Appendix B.8, p. 35 ('Since α* is the optimal performance achievable in the i.i.d. model (see the Introduction), we also have α(p) ≤ α*'); Introduction p. 3 citing Kaplan, Naori & Raz, Theorem 3.4

import Mathlib
import Definitions.Def_SampleDrivenOS_Limit_Setting

open MeasureTheory Filter Topology

namespace SampleDrivenOS.Limit

/-- Theorem 8 (p. 17), upper bound `α(p) ≤ α*`: for every `p ∈ (0, 1)`, the optimal value
`α(p)` of SDCLP_p is at most the i.i.d. prophet constant `α*`, the solution in `(0, 1)` of
`∫_0^1 1 / (y(1 - ln y) + 1/α* - 1) dy = 1`. -/
theorem sdclpValue_le_alphaStar (p s : ℝ) (hp : p ∈ Set.Ioo (0:ℝ) 1) (hs : IsAlphaStar s) :
    sdclpValue p ≤ s := by sorry

end SampleDrivenOS.Limit
