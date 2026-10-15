-- Prove2me | Theorems.Thm_SampleDrivenOS_Linear_b9_reduction
-- name    : SampleDrivenOS.Linear.b9_reduction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:01:31.236647+00:00
-- url     : https://prove2.me/theorems/a95237c1-0f7f-4ca1-a2f8-3c022bc8e384
-- title:
--   B.9, p. 35 — (19) evaluated at $\alpha^*p$ with ≤ implies $\tilde\alpha(p)\ge\alpha^*p$
-- statement:
--   Let $p\in(0,1)$ and let $a$ be a root of (19), i.e. $0<a<1$ and
--   $$\ln p+\frac{a(1-p)^2}{p}=\sum_{i=1}^{\infty}\frac{\ln\bigl(1-a+a[(i+1)p^i-ip^{i+1}]\bigr)}{i(i+1)}.$$
--   Let $s>0$ with $sp<1$. If
--   $$\ln p+s(1-p)^2\le\sum_{i=1}^{\infty}\frac{\ln\bigl(1-sp+sp[(i+1)p^i-ip^{i+1}]\bigr)}{i(i+1)},$$
--   then $sp\le a$.
--
--   Writing $a=f\,p$, equation (19) becomes $\ln p+f(1-p)^2=\sum_i\ln(1-fp+fp[(i+1)p^i-ip^{i+1}])/(i(i+1))$, whose left side increases and whose right side decreases in $f$; so the displayed inequality at $f=s$ forces $s\le a/p$. With $s=\alpha^*$ this reduces Theorem 9 to the displayed inequality.
--
--   **Formalization Note** The paper writes $f(p)=\tilde\alpha(p)/p$ and concludes $f(p)\ge\alpha^*$; the statement is phrased as $sp\le a$ to avoid the division and holds for every root $a$ of (19). The hypothesis $sp<1$ keeps every logarithm's argument positive (at least $1-sp$); $\alpha^*p<1$ holds since $\alpha^*<1$. The series are Lean `tsum`s over `i : ℕ` with $i$ shifted by one; both are summable in this range.
-- source:
--   Correa, Cristi, Epstein & Soto, Sample-Driven Optimal Stopping: From the Secretary Problem to the i.i.d. Prophet Inequality, arXiv:2011.06516v2, p. 35, B.9 (Proof of Theorem 9), first paragraph and its two displays

import Mathlib
import Definitions.Def_SampleDrivenOS_Linear_Setting

namespace SampleDrivenOS.Linear

theorem b9_reduction (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) (a : ℝ) (ha : SampleDrivenOS.Limit.IsAlphaTilde p a)
    (s : ℝ) (hs0 : 0 < s) (hsp : s * p < 1)
    (h : Real.log p + s * (1 - p) ^ 2 ≤
      ∑' i : ℕ, Real.log (1 - s * p + s * p * ((i + 2) * p ^ (i + 1) - (i + 1) * p ^ (i + 2))) /
        ((i + 1) * (i + 2))) :
    s * p ≤ a := by sorry

end SampleDrivenOS.Linear
