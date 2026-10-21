-- Prove2me | Theorems.Thm_StartupExit_ExitChoice_lemma_5
-- name    : StartupExit.ExitChoice.lemma_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T04:15:43.41701+00:00
-- url     : https://prove2.me/theorems/2c1dfd63-80d3-459e-884d-44c830b2fb18
-- title:
--   Lemma 5, p. 14 — if φ(R − c) > θ₀, Π^F = Π^E for θ ≤ kink/φ, strictly decreasing on [kink/φ, θ₀/φ], strictly increasing on [θ₀/φ, 1]
-- statement:
--   Assume the standing assumptions, let $\kappa=\frac{w-1}{w+X(2,n)+\pi_B(n)}$, and let $\theta_0\in(\kappa,1)$ be the threshold of Lemma A2.1: for $\theta\in(\kappa,1]$, inequality (A2.1) holds iff $\theta\ge\theta_0$. Let $c\in[0,R]$ be small enough that $\phi:=\phi(R-c)>\theta_0$. Then the profit from flexibility $\theta\mapsto\Pi^F(c,\theta)$ on $[0,1]$ satisfies
--
--   1. $\Pi^F(c,\theta)=\Pi^E=w+X(2,m)$ whenever $\theta\le\dfrac{w-1}{\phi\,[w+X(2,n)+\pi_B(n)]}$;
--   2. it is strictly decreasing on $\bigl[\kappa/\phi,\ \theta_0/\phi\bigr]$ and strictly increasing on $\bigl[\theta_0/\phi,\ 1\bigr]$.
--
--   So for a small cost of trying the early market, flexibility pays the early-commitment profit for low $\theta$, then first declines and then increases with $\theta$.
--
--   **Formalization Note** "Let $c$ be small enough" is made precise as in the proof (Online Appendix A2, PDF 35): "Denote the unique value of $c$ for which $\phi=\theta_0$ by $c_0$. Then, the proposition holds for $c<c_0$", i.e. $\phi(R-c)>\theta_0$. $\theta_0$ is passed with its Lemma A2.1 property as a hypothesis rather than as an existential constant, so the statement cannot be met by a degenerate choice of $c_0$. $n$ is finite.
-- source:
--   Arora, Fosfuri & Rønde, Waiting for the payday? The market for startups and the timing of entrepreneurial exit, SSRN 3611808 (forthcoming in Management Science), p. 14 (PDF 15), Lemma 5; proof in Online Appendix A2 (PDF 35)

import Mathlib
import Definitions.Def_StartupExit_ExitChoice_Model

namespace StartupExit.ExitChoice

theorem lemma_5 (P : Params) (hS : P.Standing) (θ0 : ℝ)
    (hθ0 : kink P < θ0 ∧ θ0 < 1 ∧
      ∀ θ ∈ Set.Ioc (kink P) 1,
        (θ * piB P.n * (1 + piB P.n / (P.w + X2 P.n)) ≤
            Gcdf (vStar P θ) P.m / gdens (vStar P θ) P.m ↔ θ0 ≤ θ))
    (c : ℝ) (hc : c ∈ Set.Icc 0 P.R) (hφ : θ0 < P.φ (P.R - c)) :
    (∀ θ ∈ Set.Icc (0 : ℝ) 1, θ ≤ kink P / P.φ (P.R - c) → PiF P c θ = PiE P) ∧
    StrictAntiOn (PiF P c) (Set.Icc (kink P / P.φ (P.R - c)) (θ0 / P.φ (P.R - c))) ∧
    StrictMonoOn (PiF P c) (Set.Icc (θ0 / P.φ (P.R - c)) 1) := by sorry

end StartupExit.ExitChoice
