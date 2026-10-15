-- Prove2me | Theorems.Thm_VerticalOwnership_CheapTalk_theorem_2
-- name    : VerticalOwnership.CheapTalk.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:41:09.205648+00:00
-- url     : https://prove2.me/theorems/b265b9cd-4fda-4e7e-9225-95b13ee9cf38
-- title:
--   Theorem 2, pp. 13–14 — truthful cheap talk holds iff β ≥ β̳ = z_r/(1−z_r)((1−z_s)/(R(Δ)−z_s) − 1), and only if Δ ≥ Δ̳
-- statement:
--   In the model of the mission, the retailer privately observes the market state $i\in\{L,H\}$, places no advance order, and sends a message; if believed, the supplier builds $K_L=\mu_L+F^{-1}(z_s)$ or $K_H=\mu_H+F^{-1}(z_s)$. Sharing the true market condition via cheap talk is possible when both truth-telling conditions hold:
--   $$\text{(12)}\quad v_r(0,K_H\mid\mu_H)\ge v_r(0,K_L\mid\mu_H),\qquad \text{(13)}\quad v_r(0,K_L\mid\mu_L)\ge v_r(0,K_H\mid\mu_L).$$
--   Let $\Delta=\mu_H-\mu_L$, $R(d)=\frac1d\int_{F^{-1}(z_s)}^{d+F^{-1}(z_s)}F(x)\,dx$ and
--   $$\underline{\underline{\beta}}=\frac{\pi_r(0,K_H\mid\mu_L)-\pi_r(0,K_L\mid\mu_L)}{\pi_s(K_L\mid\mu_L,0)-\pi_s(K_H\mid\mu_L,0)} .$$
--   Then:
--   1. condition (12) holds for every $\beta\in[0,1]$;
--   2. **(i)** for every $\beta\in[0,1]$, cheap talk is possible, i.e. (12) and (13) hold, if and only if $\beta\ge\underline{\underline{\beta}}$;
--   3. $\underline{\underline{\beta}}=\dfrac{z_r}{1-z_r}\left(\dfrac{1-z_s}{R(\Delta)-z_s}-1\right)$ and $R(\Delta)<1$;
--   4. **(ii)** for every $\beta\in(0,1]$ there is a unique $\underline{\underline{\Delta}}>0$ with
--   $$R(\underline{\underline{\Delta}})=z_s+\frac{1-z_s}{1+\beta(1/z_r-1)},$$
--   i.e. $\underline{\underline{\Delta}}=R^{-1}\big(z_s+\frac{1-z_s}{1+\beta(1/z_r-1)}\big)$, and cheap talk is possible only if $\Delta\ge\underline{\underline{\Delta}}$.
--
--   Without partial vertical ownership ($\beta=0$) truthful cheap talk is impossible, while a sufficiently large share, or a sufficiently large information gap, makes it an equilibrium.
--
--   **Formalization Note** Part (i) is stated as an equivalence, which is what the paper's proof establishes ("possible when" in the printed statement). Part (ii) is stated for $\beta\in(0,1]$: at $\beta=0$ the argument of $R^{-1}$ equals $1$, outside the range $(z_s,1)$ of $R$, so $\underline{\underline{\Delta}}$ is undefined there; instead of a junk inverse, $\underline{\underline{\Delta}}$ is characterised as the unique positive root, whose existence and uniqueness are part of the claim. The standing assumptions (including the added $c>0$, integrability of $\varepsilon$ and strict increase of $F$ on its support) are hypotheses.
-- source:
--   Avinadav, Shamir, Partial Vertical Ownership, Capacity Investment and Information Exchange in a Supply Chain, author manuscript of 2022-06-06 (Management Science, doi:10.1287/mnsc.2023.4673), pp. 13–14, Theorem 2, (12)–(16); proof pp. 45–46

import Mathlib
import Definitions.Def_VerticalOwnership_CheapTalk_Setting

open MeasureTheory ProbabilityTheory Filter Topology

namespace VerticalOwnership.CheapTalk

theorem theorem_2 (M : Model) (hM : M.Standing) :
    (∀ β ∈ Set.Icc (0 : ℝ) 1, M.cond12 β) ∧
    (∀ β ∈ Set.Icc (0 : ℝ) 1, (M.cond12 β ∧ M.cond13 β) ↔ M.betaCT ≤ β) ∧
    M.betaCT = M.zr / (1 - M.zr) * ((1 - M.zs) / (M.R M.Δ - M.zs) - 1) ∧
    M.R M.Δ < 1 ∧
    (∀ β ∈ Set.Ioc (0 : ℝ) 1, ∃! d : ℝ, 0 < d ∧ M.R d = M.theta β) ∧
    (∀ β ∈ Set.Ioc (0 : ℝ) 1, ∀ d : ℝ, 0 < d → M.R d = M.theta β →
      (M.cond12 β ∧ M.cond13 β) → d ≤ M.Δ) := by sorry

end VerticalOwnership.CheapTalk
