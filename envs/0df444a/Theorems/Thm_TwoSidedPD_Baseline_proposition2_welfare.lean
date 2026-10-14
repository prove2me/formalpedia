-- Prove2me | Theorems.Thm_TwoSidedPD_Baseline_proposition2_welfare
-- name    : TwoSidedPD.Baseline.proposition2_welfare
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T03:08:19.182308+00:00
-- url     : https://prove2.me/theorems/e941e759-2c11-4d47-9b62-b85f0822ff7f
-- title:
--   Proposition 2, p. 3346 — price discrimination raises profit, buyer, low-type seller surplus and welfare; high types gain iff b > b̂ (then strict Pareto)
-- statement:
--   Consider a monopoly platform serving a mass one of buyers, who get a stand-alone value $v$ and a benefit $b$ per seller on the platform, and two categories of sellers $L,H$ of mass one each, who earn $\theta_j$ per buyer, with $\theta_H>\theta_L>0$ and $b>0$. Outside options are uniform on $[0,1]$. Assume Assumption 1:
--   $$0<v<4-(b+\theta_L)^2-(b+\theta_H)^2,\qquad \frac{\theta_H-3\theta_L}{2}<b .$$
--   Under uniform pricing the platform chooses $(N_B,N_S)$ to maximize $\Pi^U$; under price discrimination it chooses $(N_B,N_L,N_H)$ to maximize $\Pi^D$. Both problems have a solution, and for every uniform optimum and every discrimination optimum:
--
--   1. (i) the platform, buyers and low-type sellers are better off under price discrimination: $\Pi^U<\Pi^D$, $CS^U<CS^D$, $DS^U_L<DS^D_L$;
--   2. (ii) total welfare is higher under price discrimination: $SW^U<SW^D$;
--   3. (iii) high-type sellers are better off under price discrimination if and only if
--   $$b>\hat b(\theta_H,\theta_L)\equiv\frac{\sqrt{32-7(\theta_H-\theta_L)^2}-3\theta_H-\theta_L}{4};$$
--   4. in this case price discrimination is a strict Pareto improvement over uniform pricing: the platform, the buyers, the low-type and the high-type sellers are all strictly better off.
--
--   This is the paper's main welfare result: unlike the classical one-sided analysis with linear demands, seller-side price discrimination by a two-sided platform raises total welfare and can benefit every group.
--
--   **Formalization Note.** Equilibria are global maximizers of $\Pi^U$ over $\mathbb R^2$ and of $\Pi^D$ over $\mathbb R^3$ (the objects the first-order conditions (7)–(11) solve), not points in $[0,1]^n$. "Better off" means a strictly higher profit for the platform and strictly higher surplus for buyers and sellers, with surpluses defined by the integrals of App. A.2. $b>0$ is the standing assumption of §3.2 and footnote 10. Assumption 1(i) is used as printed ($v<\dots$); the paper's bound $\bar b$ (p. 3344) corresponds to $2v<\dots$, which is what interior buyer participation $N^D_B=2v/D<1$ needs, so the printed assumption does not by itself keep participation in $(0,1)$; the statement does not claim it does. On the parameter region $32-7(\theta_H-\theta_L)^2>0$, so `Real.sqrt` is the ordinary square root.
-- source:
--   de Cornière, Mantovani & Shekhar, Third-Degree Price Discrimination in Two-Sided Markets, Management Science 71(4) (2025), p. 3346, §4.3.1, Proposition 2; proof App. A.2, pp. 3352–3353

import Mathlib
import Definitions.Def_TwoSidedPD_Baseline_Setting

namespace TwoSidedPD.Baseline

theorem proposition2_welfare (v b θH θL : ℝ) (hL : 0 < θL) (hLH : θL < θH) (hb : 0 < b)
    (hA : Assumption1 v b θH θL) :
    ((∃ x : ℝ × ℝ, IsUniformOpt v b θH θL x) ∧ (∃ y : ℝ × ℝ × ℝ, IsDiscrOpt v b θH θL y)) ∧
    ∀ (x : ℝ × ℝ) (y : ℝ × ℝ × ℝ), IsUniformOpt v b θH θL x → IsDiscrOpt v b θH θL y →
      -- (i) platform, buyers and low-type sellers are strictly better off
      (profitU v b θH θL x < profitD v b θH θL y ∧
        buyerSurplusU v b θH θL x < buyerSurplusD v b θH θL y ∧
        sellerSurplusU θL θH θL x < sellerSurplusDL θL y) ∧
      -- (ii) total welfare is strictly higher
      welfareU v b θH θL x < welfareD v b θH θL y ∧
      -- (iii) high-type sellers are strictly better off iff b > b̂(θH, θL)
      (sellerSurplusU θH θH θL x < sellerSurplusDH θH y ↔ bhat θH θL < b) ∧
      -- in that case, a strict Pareto improvement
      (bhat θH θL < b →
        profitU v b θH θL x < profitD v b θH θL y ∧
        buyerSurplusU v b θH θL x < buyerSurplusD v b θH θL y ∧
        sellerSurplusU θL θH θL x < sellerSurplusDL θL y ∧
        sellerSurplusU θH θH θL x < sellerSurplusDH θH y) := by sorry

end TwoSidedPD.Baseline
