-- Prove2me | Theorems.Thm_SampleDrivenOS_Linear_theorem_9
-- name    : SampleDrivenOS.Linear.theorem_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:01:25.588984+00:00
-- url     : https://prove2.me/theorems/03c7bc04-4936-45c1-b8c6-a1ceb23b227c
-- title:
--   Theorem 9, p. 17 — for $p\in(0,1)$, $\tilde\alpha(p)\ge\alpha^*p$
-- statement:
--   Let $p\in(0,1)$. Let $\tilde\alpha(p)\in(0,1)$ be a solution of
--   $$\ln p+\frac{\tilde\alpha(1-p)^2}{p}=\sum_{i=1}^{\infty}\frac{\ln\bigl(1-\tilde\alpha+\tilde\alpha[(i+1)p^i-ip^{i+1}]\bigr)}{i(i+1)}\tag{19}$$
--   and let $\alpha^*\in(0,1)$ be a solution of $\int_0^1 dy/(y(1-\ln y)+1/\alpha^*-1)=1$. Then
--   $$\tilde\alpha(p)\ge\alpha^*p.$$
--
--   In the $p$-sample-driven optimal stopping problem a random set of items, each independently with probability $p$, is revealed in advance as a sample, and the algorithm must stop on the best of the remaining items. The explicit threshold rule of §4.3 has competitive ratio at least $\tilde\alpha(p)$, so Theorem 9 shows this ratio lies above the line from $0$ to the i.i.d. prophet constant $\alpha^*\approx 0.745$. Taking $p=1-\varepsilon$ yields a guarantee of $\alpha^*-O(\varepsilon)$ with $O(n/\varepsilon)$ samples.
--
--   **Formalization Note** $\tilde\alpha(p)$ and $\alpha^*$ enter through the predicates `IsAlphaTilde p a` and `IsAlphaStar s`, and the statement holds for every solution $a$ of (19) and every solution $s$ of the $\alpha^*$ equation. Their existence and uniqueness (Lemma 7 of the paper; `CorreaThreshold.Adaptive.beta_star_existsUnique` for $\alpha^*=1/\beta^*$) are not assumed and not needed; both exist, so the statement is not vacuous. The series is a Lean `tsum` over `i : ℕ` with the index shifted by one.
-- source:
--   Correa, Cristi, Epstein & Soto, Sample-Driven Optimal Stopping: From the Secretary Problem to the i.i.d. Prophet Inequality, arXiv:2011.06516v2, p. 17, Theorem 9

import Mathlib
import Definitions.Def_SampleDrivenOS_Linear_Setting

namespace SampleDrivenOS.Linear

theorem theorem_9 (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) (a : ℝ) (ha : SampleDrivenOS.Limit.IsAlphaTilde p a)
    (s : ℝ) (hs : SampleDrivenOS.Limit.IsAlphaStar s) : s * p ≤ a := by sorry

end SampleDrivenOS.Linear
