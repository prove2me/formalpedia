-- Prove2me | Theorems.Thm_PhiDivRobust_Barrier_den_hertog_lemma_A2
-- name    : PhiDivRobust.Barrier.den_hertog_lemma_A2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T18:56:30.092336+00:00
-- url     : https://prove2.me/theorems/54772baa-97fc-45a1-ac6f-e10c36569d94
-- title:
--   den Hertog (1994), Lemma A.2, as quoted — (36) with β implies (1 + β/3)-self-concordance of the barrier
-- statement:
--   Let $f:\mathbb R\to\mathbb R$ be convex and three times continuously differentiable on $(0,\infty)$, let $g(s,y)=yf(s/y)$, and let $\beta\ge 0$ be such that (36) holds:
--
--   $$\bigl|\nabla^3 g(s,y)[h,h,h]\bigr|\le\beta\,h^{\mathsf T}\nabla^2 g(s,y)h\,\sqrt{\frac{h_1^2}{s^2}+\frac{h_2^2}{y^2}}\qquad\text{for all } s>0,\ y>0,\ h\in\mathbb R^2.$$
--
--   Then the logarithmic barrier $\varphi_B(s,y,z)=-\ln(z-yf(s/y))-\ln s-\ln y$ of the set (34) is
--
--   $$\Bigl(1+\tfrac13\beta\Bigr)\text{-self-concordant}$$
--
--   on its domain $F_f=\{(s,y,z):s>0,\ y>0,\ yf(s/y)<z\}$ (Definition 1). In particular $F_f$ is open and convex and $\varphi_B$ is $C^3$ on it.
--
--   This is the compatibility lemma the paper imports from den Hertog's 1994 monograph; it reduces self-concordance of a barrier in three variables to a two-variable differential inequality for $g$.
--
--   **Formalization Note** The page says "if there exists a $\beta$"; the hypothesis $\beta\ge0$ is added because the statement is false for negative $\beta$: for $f\equiv0$ inequality (36) holds for every $\beta$ (both sides vanish), and $\beta=-3$ would make $-\ln z-\ln s-\ln y$ $0$-self-concordant, i.e. with vanishing third differential, which it is not. The paper applies the lemma only with $\beta=3+\kappa\sqrt2>0$. Convexity and $C^3$ regularity of $f$ on $(0,\infty)$ are the hypotheses of Theorem 2, in whose proof the lemma is quoted.
-- source:
--   Ben-Tal, den Hertog, De Waegenaere, Melenberg, Rennen, Robust Solutions of Optimization Problems Affected by Uncertain Probabilities, Management Sci. 59(2), 2013, p. 350, proof of Theorem 2, Eq. (36) and the sentence quoting Lemma A.2 of den Hertog (1994), Interior Point Approach to Linear, Quadratic and Convex Programming, Kluwer

import Mathlib
import Definitions.Def_PhiDivRobust_Barrier_IsSelfConcordant
import Definitions.Def_PhiDivRobust_Barrier_perspective
import Definitions.Def_PhiDivRobust_Barrier_logBarrier

namespace PhiDivRobust.Barrier

theorem den_hertog_lemma_A2 (f : ℝ → ℝ) (β : ℝ)
    (hconv : ConvexOn ℝ (Set.Ioi 0) f) (hf : ContDiffOn ℝ 3 f (Set.Ioi 0)) (hβ : 0 ≤ β)
    (h36 : ∀ s y : ℝ, 0 < s → 0 < y → ∀ h : ℝ × ℝ,
      |iteratedFDeriv ℝ 3 (perspective f) (s, y) (fun _ => h)| ≤
        β * iteratedFDeriv ℝ 2 (perspective f) (s, y) (fun _ => h) *
          Real.sqrt (h.1 ^ 2 / s ^ 2 + h.2 ^ 2 / y ^ 2)) :
    IsSelfConcordant (1 + β / 3) (barrierDomain f) (logBarrier f) := by sorry

end PhiDivRobust.Barrier
