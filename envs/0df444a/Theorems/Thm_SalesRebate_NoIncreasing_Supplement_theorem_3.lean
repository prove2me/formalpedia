-- Prove2me | Theorems.Thm_SalesRebate_NoIncreasing_Supplement_theorem_3
-- name    : SalesRebate.NoIncreasing.Supplement.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T03:20:15.83417+00:00
-- url     : https://prove2.me/theorems/2bc89fbe-3d3a-4f1c-abcf-a6b94847392a
-- title:
--   Theorem 3, p. 18 (PDF 18) — the optimal spread-constrained program exists and is rM·1{v ≤ vc}, with (c, vc) solving the two displayed equations
-- statement:
--   Let $(\theta,\sigma_\theta,\sigma_\epsilon)$ be a valid model of §II ($v\sim N(\theta,\sigma_\theta^2)$ the common quality, $\epsilon_i\sim N(0,\sigma_\epsilon^2)$ the tastes, $\sigma_\theta,\sigma_\epsilon>0$), with $\sigma^2=\sigma_\epsilon^2+\sigma_\theta^2$, $\tau=\sigma_\theta^2/\sigma^2$, $\sigma_v=\sigma_\epsilon\sigma_\theta/\sigma$ and $\mu_c=\tau c+(1-\tau)\theta$, and let $p$ be a market price satisfying Assumption 1 ($p$ maximizes $x\Phi((\theta-x)/\sigma)$ over $x\ge0$). Here $\Phi,\phi$ are the standard normal CDF and density, $\mathbb E_{v\mid v_i=x}$ is the expectation under the posterior $N(\tau x+(1-\tau)\theta,\sigma_v^2)$, and the expected profit of a reward $\hat r$ (a function of the quality) with cutoff $c$ is (2): $\mathbb E_v[\Pi(p,\hat r)]=\mathbb E_v[(p-\hat r(v))\Phi((v-c)/\sigma_\epsilon)]$.
--
--   The **spread-constrained problem** (p. 18) maximizes the expected profit over pairs $(\hat r,c)$ with $\hat r:\mathbb R\to[0,p]$ measurable, $r_{\max}-r_{\min}\le\sqrt{2\pi}\,\sigma_\epsilon\sigma/\sigma_\theta$ (largest minus smallest reward), and $c+\mathbb E_{v\mid v_i=c}[\hat r(v)]=p$. Let $r_M=\min(p,\sqrt{2\pi}\,\sigma_\epsilon\sigma/\sigma_\theta)$. Then the problem has an optimal pair, and for every optimal pair $(\hat r^*_{SC},c)$ there is $v_c\in\mathbb R$ with
--   $$\hat r^*_{SC}(v)=r_M\,\mathbf 1\{v\le v_c\}\quad\text{for almost every }v,$$
--   $$p=c+r_M\,\Phi\Big(\frac{v_c-\mu_c}{\sigma_v}\Big),\qquad \frac{\Phi\big(\frac{v_c-c}{\sigma_\epsilon}\big)}{\phi\big(\frac{v_c-c}{\sigma_\epsilon}\big)/\sigma_\epsilon}=\frac{c}{1-\tau r_M\,\phi\big(\frac{v_c-\mu_c}{\sigma_v}\big)/\sigma_v}.$$
--
--   The optimal spread-constrained program pays a fixed rebate of size $r_M$ when the realized quality is at most a threshold and nothing otherwise.
--
--   **Formalization Note** The right-hand denominator is $\ge0$ under the spread bound ($\tau r_M\phi/\sigma_v\le\tau\sigma_\epsilon\sigma/(\sigma_\theta\sigma_v)=1$); at $0$ Lean's $c/0=0$ would contradict the positive left side, matching the paper, where the right side would be infinite.
--
--   Differences from the source:
--   - reading: 'the optimal reward program r̂*SC(·) with the spread constraint is of the form …' → an optimal pair exists, and every optimal pair has the stated form; reason: the definite article presupposes an optimum; posing only 'every optimum has the form' would be vacuous if none existed, so existence is part of the claim (the appendix proves it)
--   - encoding: rmax − rmin ≤ √(2π)σϵσ/σθ, with rmin, rmax the minimum and maximum reward → ∀ v w, r̂ v − r̂ w ≤ spreadBound M; reason: every pairwise difference is bounded by the bound iff sup r̂ − inf r̂ is; this avoids real sSup/sInf junk values
--   - encoding: r̂*SC(v) = rM × 1{v ≤ vc} → r̂ =ᵐ[volume] (fun v => if v ≤ vc then rM M p else 0); reason: the SC problem's objective and constraint do not see a change of r̂ on a null set that keeps its values in [0, rM], so an optimum is determined only almost everywhere
--   - reading: (c, vc) is the solution of the two displayed equations → the cutoff c of every optimal pair and some real vc satisfy the two equations; reason: the paper does not prove that the system has a unique solution; the statement asserts what the optimum satisfies, not uniqueness of the system's solution
--   - encoding: standing assumptions of §II (Gaussian laws) and Assumption 1 for the price p → hM : M.Valid (σθ, σε > 0) and hp : M.IsMarketPrice p (maximization clause over x ≥ 0) from the published Setting; reason: the page's Gaussian laws and its divisions by σε, σθ presuppose positive deviations, and p is defined by Assumption 1 throughout the paper; no instance of the paper's setting is excluded
-- source:
--   Ajorlou, Jadbabaie, Sales-Based Rebate Design, arXiv:1902.09646v4, p. 18, Theorem 3 (spread-constrained problem, p. 18)

import Mathlib
import Definitions.Def_BlackScholesModel_Core
import Definitions.Def_SalesRebate_NoIncreasing_Setting
import Definitions.Def_SalesRebate_NoIncreasing_Supplement_Problems

namespace SalesRebate.NoIncreasing.Supplement

open MeasureTheory ProbabilityTheory BlackScholesModel Filter Topology

theorem theorem_3 (M : Model) (hM : M.Valid) (p : ℝ) (hp : M.IsMarketPrice p) :
    (∃ rhat c, IsOptimalSC M p rhat c) ∧
      ∀ rhat c, IsOptimalSC M p rhat c → ∃ vc : ℝ,
        (rhat =ᵐ[volume] fun v => if v ≤ vc then rM M p else 0) ∧
        p = c + rM M p * stdNormalCDF ((vc - M.postMean c) / sigmaV M) ∧
        stdNormalCDF ((vc - c) / M.σε) / (stdNormalPDF ((vc - c) / M.σε) / M.σε) =
          c / (1 - M.tau * rM M p * (stdNormalPDF ((vc - M.postMean c) / sigmaV M) / sigmaV M)) := by sorry

end SalesRebate.NoIncreasing.Supplement
