-- Prove2me | Theorems.Thm_SampleDrivenOS_Linear_b9_equiv_a
-- name    : SampleDrivenOS.Linear.b9_equiv_a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:01:19.190462+00:00
-- url     : https://prove2.me/theorems/14d1c9f0-7bd2-4bb1-8411-c9538202204e
-- title:
--   B.9, p. 36 — the reduced inequality is equivalent to $\alpha^*\le a(p)$
-- statement:
--   Let $p\in(0,1)$ and $s\in(0,1)$, and let
--   $$a(p)=\sum_{i=1}^{\infty}\frac{\ln\bigl(\tfrac1p-s(1-p^i(1+i(1-p)))\bigr)}{i(i+1)}+s(2p-p^2).$$
--   Then
--   $$\ln p+s(1-p)^2\le\sum_{i=1}^{\infty}\frac{\ln\bigl(1-sp+sp[(i+1)p^i-ip^{i+1}]\bigr)}{i(i+1)}\iff s\le a(p).$$
--
--   With $s=\alpha^*$ the left side is the inequality to which Theorem 9 was reduced, and the right side is the form in which it is proved: $a(1)=\alpha^*$ and $a$ is decreasing on $(0,1]$.
--
--   **Formalization Note** The paper obtains the equivalence "by subtracting $\ln p$", using $\sum_{i\ge1}1/(i(i+1))=1$ and $\ln(1-sp+sp\,w)=\ln p+\ln(1/p-s(1-w))$. The function $a$ depends on $s$ (the paper's $\alpha^*$) as a parameter, `aB9 s p`. All series are Lean `tsum`s with the index shifted by one, summable for $s,p\in(0,1)$; summability is part of what is to be proved, not a hypothesis.
-- source:
--   Correa, Cristi, Epstein & Soto, Sample-Driven Optimal Stopping: From the Secretary Problem to the i.i.d. Prophet Inequality, arXiv:2011.06516v2, p. 36, B.9 (Proof of Theorem 9), first display

import Mathlib
import Definitions.Def_SampleDrivenOS_Linear_Setting

namespace SampleDrivenOS.Linear

theorem b9_equiv_a (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) (s : ℝ) (hs : s ∈ Set.Ioo (0 : ℝ) 1) :
    (Real.log p + s * (1 - p) ^ 2 ≤
      ∑' i : ℕ, Real.log (1 - s * p + s * p * ((i + 2) * p ^ (i + 1) - (i + 1) * p ^ (i + 2))) /
        ((i + 1) * (i + 2))) ↔ s ≤ aB9 s p := by sorry

end SampleDrivenOS.Linear
