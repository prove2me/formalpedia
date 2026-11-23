-- Prove2me | Theorems.Thm_SalesRebate_NoIncreasing_Supplement_theorem_4
-- name    : SalesRebate.NoIncreasing.Supplement.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T03:20:43.449286+00:00
-- url     : https://prove2.me/theorems/01d787be-0a3f-4258-bc42-8d45cb839403
-- title:
--   Theorem 4, pp. 19–20 (PDF 19–20) — the optimal rate-constrained program exists and is saturated linear (corrected: cφ(θ − c) read as cφ((θ−c)/σ)/σ)
-- statement:
--   Let $(\theta,\sigma_\theta,\sigma_\epsilon)$ be a valid model of §II ($v\sim N(\theta,\sigma_\theta^2)$ the common quality, $\epsilon_i\sim N(0,\sigma_\epsilon^2)$ the tastes, $\sigma_\theta,\sigma_\epsilon>0$), with $\sigma^2=\sigma_\epsilon^2+\sigma_\theta^2$, $\tau=\sigma_\theta^2/\sigma^2$, $\sigma_v=\sigma_\epsilon\sigma_\theta/\sigma$ and $\mu_c=\tau c+(1-\tau)\theta$, and let $p$ be a market price satisfying Assumption 1 ($p$ maximizes $x\Phi((\theta-x)/\sigma)$ over $x\ge0$). Here $\Phi,\phi$ are the standard normal CDF and density, $\mathbb E_{v\mid v_i=x}$ is the expectation under the posterior $N(\tau x+(1-\tau)\theta,\sigma_v^2)$, and the expected profit of a reward $\hat r$ (a function of the quality) with cutoff $c$ is (2): $\mathbb E_v[\Pi(p,\hat r)]=\mathbb E_v[(p-\hat r(v))\Phi((v-c)/\sigma_\epsilon)]$.
--
--   The **rate-constrained problem** ((29), p. 34) maximizes the expected profit over pairs $(\hat r,c)$ with $\hat r:\mathbb R\to[0,p]$ continuous and piecewise continuously differentiable, $|\tfrac{d}{dv}\hat r(v)|\le1/\tau$ off its break points, and $c+\mathbb E_{v\mid v_i=c}[\hat r(v)]=p$. Then the problem has an optimal pair, and for every optimal pair $(\hat r^*_{RC},c)$ there are $v_L,v_H\in\mathbb R$ with
--   $$\hat r^*_{RC}(v)=\begin{cases}p,&v<v_L,\\ p-\frac1\tau(v-v_L),&v_L\le v<v_H,\\ 0,&v_H\le v,\end{cases}$$
--   and, writing $z_L=(v_L-\mu_c)/\sigma_v$, $z_H=(v_H-\mu_c)/\sigma_v$ and $\psi(c)=\phi((\theta-c)/\sigma)/\sigma$,
--   $$\frac{\int_{v_L}^{v_H}\Phi\big(\frac{w-c}{\sigma_\epsilon}\big)\frac{\phi\big(\frac{\theta-w}{\sigma_\theta}\big)}{\sigma_\theta}\,dw}{\Phi(z_H)-\Phi(z_L)}=\frac{c\,\psi(c)}{1+\Phi(z_L)-\Phi(z_H)},\qquad v_H-v_L=\tau p,$$
--   $$p=c+\frac{\sigma_v}{\tau}\Big(z_H\Phi(z_H)-z_L\Phi(z_L)+\phi(z_H)-\phi(z_L)\Big).$$
--
--   The optimal rate-constrained program fully refunds below a quality threshold, decreases at the maximal rate $1/\tau$, and pays nothing above a second threshold.
--
--   **Formalization Note** The paper prints $c\phi(\theta-c)$ on the right of the first equation, its value at the normalization $\sigma=1$ used in the proof; for general $\sigma$ it is $c\,\psi(c)$ (see the differences below). Both denominators are positive: $v_H-v_L=\tau p>0$ and $\Phi<1$.
--
--   Differences from the source:
--   - correction: first equation's right side cφ(θ − c)/(1 + Φ((vL−µc)/σv) − Φ((vH−µc)/σv)) → c · ψ(c)/(1 + Φ((vL−µc)/σv) − Φ((vH−µc)/σv)) with ψ(c) = φ((θ − c)/σ)/σ (M.psi c); reason: the proof explicitly normalizes σ = 1 on p. 34, and (36) on p. 37 uses the normalized density. Rescale θ, c, p, vL, vH and all deviations by σ; τ and all CDF arguments are invariant, and c′φ(θ′−c′) = (c/σ)φ((θ−c)/σ) = cψ(c). Thus the corrected equation is exactly the normalized source equation in the original units, with no source case excluded
--   - reading: 'the optimal reward program r̂*RC(·) satisfying the rate of change constraint is of the form …' → an optimal pair exists, and every optimal pair has the stated form; reason: the definite article presupposes an optimum; posing only 'every optimum has the form' would be vacuous if none existed, so existence is part of the claim (the appendix proves it)
--   - reading: r̂ : R → [0, p] piecewise continuously differentiable with |d/dv r̂(v)| ≤ 1/τ ((29): r̂ = r0 − ∫_{−∞}^v u, u ∈ PC(R; [−1/τ, 1/τ])) → FeasibleRC: values in [0, p], r̂ continuous, C¹ off a set D with finitely many points in every bounded interval, finite left and right derivative limits at every point of D, |deriv r̂| ≤ 1/τ off D, and the indifference equation; reason: the paper uses continuous piecewise-C¹ rewards in Lemma 3 and a piecewise-continuous control u = −r̂′ in (29), p. 34; the finite one-sided derivative limits restore that class. Continuity rules out jumps, which would invalidate Lemma 3. No behavior at infinity is added to the main-text class
--   - reading: (c, vL, vH) is the solution of the three displayed equations → the cutoff c of every optimal pair and some reals vL, vH satisfy the three equations, and r̂ equals the saturated linear program everywhere; reason: the paper does not prove uniqueness of the system's solution; equality is pointwise because both r̂ and the saturated program are continuous
--   - encoding: standing assumptions of §II (Gaussian laws) and Assumption 1 for the price p → hM : M.Valid (σθ, σε > 0) and hp : M.IsMarketPrice p (maximization clause over x ≥ 0) from the published Setting; reason: the page's Gaussian laws and its divisions by σε, σθ presuppose positive deviations, and p is defined by Assumption 1 throughout the paper; no instance of the paper's setting is excluded
-- source:
--   Ajorlou, Jadbabaie, Sales-Based Rebate Design, arXiv:1902.09646v4, pp. 19–20, Theorem 4 (rate-constrained problem (29), p. 34)

import Mathlib
import Definitions.Def_BlackScholesModel_Core
import Definitions.Def_SalesRebate_NoIncreasing_Setting
import Definitions.Def_SalesRebate_NoIncreasing_Supplement_Problems

namespace SalesRebate.NoIncreasing.Supplement

open MeasureTheory ProbabilityTheory BlackScholesModel Filter Topology

theorem theorem_4 (M : Model) (hM : M.Valid) (p : ℝ) (hp : M.IsMarketPrice p) :
    (∃ rhat c, IsOptimalRC M p rhat c) ∧
      ∀ rhat c, IsOptimalRC M p rhat c → ∃ vL vH : ℝ,
        (∀ v, rhat v = rcProgram M p vL vH v) ∧
        (∫ w in vL..vH, stdNormalCDF ((w - c) / M.σε) * (stdNormalPDF ((M.θ - w) / M.σθ) / M.σθ)) /
            (stdNormalCDF ((vH - M.postMean c) / sigmaV M) -
              stdNormalCDF ((vL - M.postMean c) / sigmaV M)) =
          c * M.psi c / (1 + stdNormalCDF ((vL - M.postMean c) / sigmaV M) -
              stdNormalCDF ((vH - M.postMean c) / sigmaV M)) ∧
        vH - vL = M.tau * p ∧
        p = c + sigmaV M / M.tau *
          ((vH - M.postMean c) / sigmaV M * stdNormalCDF ((vH - M.postMean c) / sigmaV M) -
            (vL - M.postMean c) / sigmaV M * stdNormalCDF ((vL - M.postMean c) / sigmaV M) +
            stdNormalPDF ((vH - M.postMean c) / sigmaV M) -
            stdNormalPDF ((vL - M.postMean c) / sigmaV M)) := by sorry

end SalesRebate.NoIncreasing.Supplement
