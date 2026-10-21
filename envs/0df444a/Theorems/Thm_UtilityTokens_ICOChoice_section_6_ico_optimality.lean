-- Prove2me | Theorems.Thm_UtilityTokens_ICOChoice_section_6_ico_optimality
-- name    : UtilityTokens.ICOChoice.section_6_ico_optimality
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:31:32.785713+00:00
-- url     : https://prove2.me/theorems/f5980e4d-a332-47b7-9f80-7eae0951479a
-- title:
--   Section 6, (15)–(16), p. 23, and Appendix A — the ICO is optimal exactly when x ≥ x̄, never for Θ ≤ Θ̃, and x̄ falls with Θ
-- statement:
--   Fix the ICO cost $f>0$. Let $X^*_T$ and $X^*_I$ be the optimal payoffs of traditional sales and of the ICO, for type range $\Theta>1$ and network intensity $x>0$; let $\tilde\Theta=(\sqrt5+3)/2$, $\theta^*$ as in (11), and
--   $$\bar x=\frac{f}{(\theta^*-1)\Bigl[\bigl(\frac{\Theta-\theta^*}{\Theta}\bigr)^2-\frac1\Theta\Bigr]} .$$
--   The equilibrium strategy is $S^*=i$ when $X^*_i\ge X^*_{-i}$. Then:
--
--   1. **(15)** If $\Theta\in(1,\tilde\Theta]$, then $X^*_I<X^*_T$ for every $x>0$: $S^*=T$ for all $x$.
--   2. **(16)** If $\Theta\in(\tilde\Theta,3]$, then $\bar x>0$ and, for every $x>0$,
--   $$S^*=\begin{cases}T, & x<\bar x,\\ I, & x\ge\bar x,\end{cases}\qquad\text{i.e.}\qquad X^*_T\le X^*_I\iff x\ge\bar x .$$
--   3. The threshold $\bar x$ is strictly decreasing in $\Theta$ on $(\tilde\Theta,3]$.
--
--   This is the paper's main result: token-based sales become optimal when network effects are strong enough, and the required network intensity falls as entrepreneurial ability (the type range $\Theta$) rises.
--
--   **Formalization Note** The paper prints the ranges as $[1,\tilde\Theta]$ and $[\tilde\Theta,3]$. $\Theta=1$ is excluded by the standing assumption $\Theta>1$, and at $\Theta=\tilde\Theta$ one has $\theta^*=1$, so the denominator of $\bar x$ vanishes; the statement assigns $\Theta=\tilde\Theta$ to the first case, where it belongs. Case (15) is stated strictly ($X^*_I<X^*_T$), which needs $f>0$. In case (16) the equivalence is stated together with $\bar x>0$, so that it cannot hold with a non-positive threshold.
-- source:
--   Shakhnov & Zaccaria, Utility Tokens, Network Effects, and Pricing Power, SSRN working paper 3613261 (PDF of 2023-04-23), p. 23, Section 6, (15)–(16); p. 35, Appendix A

import Mathlib
import Definitions.Def_UtilityTokens_ICOChoice_Setting

namespace UtilityTokens.ICOChoice

theorem section_6_ico_optimality (f : ℝ) (hf : 0 < f) :
    (∀ Θ x : ℝ, 1 < Θ → Θ ≤ thetaTilde → 0 < x → optPayoffI Θ x f < optPayoffT Θ x) ∧
    (∀ Θ : ℝ, thetaTilde < Θ → Θ ≤ 3 →
      0 < xbar Θ f ∧
        ∀ x : ℝ, 0 < x → (optPayoffT Θ x ≤ optPayoffI Θ x f ↔ xbar Θ f ≤ x)) ∧
    StrictAntiOn (fun Θ => xbar Θ f) (Set.Ioc thetaTilde 3) := by sorry

end UtilityTokens.ICOChoice
