-- Prove2me | Theorems.Thm_StartupExit_ExitChoice_lemma_A2_1
-- name    : StartupExit.ExitChoice.lemma_A2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:15:51.551577+00:00
-- url     : https://prove2.me/theorems/4918dd03-4e38-4cd6-90cb-250d248fbd81
-- title:
--   Lemma A2.1, Online Appendix A2 — (A2.1) G(v̲*(θ),m)/g(v̲*(θ),m) ≥ θπ_B(n)(1 + π_B(n)/(w+X(2,n))) holds exactly for θ ≥ θ₀
-- statement:
--   Assume the standing assumptions and $c=0$, and write $\kappa=\frac{w-1}{w+X(2,n)+\pi_B(n)}$ for the kink, above which $\underline v^*(\theta)>-1$. Consider the inequality
--
--   $$\frac{G(\underline v^*(\theta),m)}{g(\underline v^*(\theta),m)}\ \ge\ \theta\,\pi_B(n)\Bigl(1+\frac{\pi_B(n)}{w+X(2,n)}\Bigr). \tag{A2.1}$$
--
--   There is $\theta_0\in(\kappa,1)$ such that, for every $\theta\in(\kappa,1]$, (A2.1) holds if and only if $\theta\ge\theta_0$, and it holds strictly if and only if $\theta>\theta_0$.
--
--   By eq. (A2.2), the sign of $\partial\Pi^F/\partial\theta$ above the kink is the sign of (A2.1)'s slack, so $\theta_0$ is where the flexible profit at $c=0$ turns from decreasing to increasing.
--
--   **Formalization Note** The page says "(A2.1) holds if and only if $\theta>\theta_0$". At $\theta_0$ itself both sides are equal by continuity, so the non-strict inequality holds there too; the statement gives the corrected pair ($\ge$ iff $\theta\ge\theta_0$; $>$ iff $\theta>\theta_0$). It is stated on $(\kappa,1]$, where $g(\underline v^*(\theta),m)>0$. For $\theta\le\kappa$ the page uses the limit $G(-1,m)/g(-1,m)=0$; for $m\ge3$ both are $0$ and Lean's $0/0=0$ would decide the claim by a junk value, so that range is excluded. The $n\to\infty$ sentence is not formalized.
-- source:
--   Arora, Fosfuri & Rønde, Waiting for the payday? The market for startups and the timing of entrepreneurial exit, SSRN 3611808 (forthcoming in Management Science), Online Appendix A2 (PDF 32), Lemma A2.1, inequality (A2.1)

import Mathlib
import Definitions.Def_StartupExit_ExitChoice_Model

namespace StartupExit.ExitChoice

theorem lemma_A2_1 (P : Params) (hS : P.Standing) :
    ∃ θ0 : ℝ, kink P < θ0 ∧ θ0 < 1 ∧
      ∀ θ ∈ Set.Ioc (kink P) 1,
        (θ * piB P.n * (1 + piB P.n / (P.w + X2 P.n)) ≤
            Gcdf (vStar P θ) P.m / gdens (vStar P θ) P.m ↔ θ0 ≤ θ) ∧
        (θ * piB P.n * (1 + piB P.n / (P.w + X2 P.n)) <
            Gcdf (vStar P θ) P.m / gdens (vStar P θ) P.m ↔ θ0 < θ) := by sorry

end StartupExit.ExitChoice
