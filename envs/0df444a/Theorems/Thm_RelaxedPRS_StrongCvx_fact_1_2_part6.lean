-- Prove2me | Theorems.Thm_RelaxedPRS_StrongCvx_fact_1_2_part6
-- name    : RelaxedPRS.StrongCvx.fact_1_2_part6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T23:11:46.617877+00:00
-- url     : https://prove2.me/theorems/c9e01cce-515b-412c-b8fc-8839a0b3857a
-- title:
--   Fact 1.2(6) — fixed-point residual rates (1.10)
-- statement:
--   For a relaxed PRS run and a fixed point $z^*$, suppose the relaxation products have a positive lower bound $\tau$: $\tau\le\lambda_j(1-\lambda_j)$ for every $j$. The squared fixed-point residual obeys both
--   $$\|T_{\mathrm{PRS}}z^k-z^k\|^2\le\frac{\|z^0-z^*\|^2}{\tau(k+1)}\quad\text{and}\quad\|T_{\mathrm{PRS}}z^k-z^k\|^2=o\!\left(\frac1{\tau(k+1)}\right).$$
--   The positive lower bound is the quantitative form of the infimum hypothesis on the page.
-- source:
--   Davis & Yin, Faster convergence rates of relaxed Peaceman-Rachford and ADMM under regularity assumptions, arXiv:1407.5210v3, p. 7, Fact 1.2 Part 6, (1.10)

import Mathlib
import Definitions.Def_RelaxedPRS_StrongCvx_Setting

open scoped InnerProductSpace
open Filter Asymptotics

namespace RelaxedPRS.StrongCvx

/-- Fact 1.2(6), p. 7: both fixed-point residual rates in (1.10). -/
theorem fact_1_2_part6 {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H]
    (f g : H → EReal)
    (hf : ThreeOpSplitting.ConvexRates.IsProperClosedConvex f)
    (hg : ThreeOpSplitting.ConvexRates.IsProperClosedConvex g)
    (γ : ℝ) (hγ : 0 < γ) (Pf Pg : H → H)
    (hPf : ThreeOpSplitting.ConvexRates.IsProx γ f Pf)
    (hPg : ThreeOpSplitting.ConvexRates.IsProx γ g Pg)
    (lam : ℕ → ℝ) (hlam : ∀ k, 0 < lam k ∧ lam k ≤ 1)
    (z : ℕ → H) (hz : IsPRSRun Pf Pg lam z)
    (zs : H) (hzs : TPRS Pf Pg zs = zs)
    (τ : ℝ) (hτ : 0 < τ) (hτle : ∀ j, τ ≤ lam j * (1 - lam j)) :
    (∀ k, ‖TPRS Pf Pg (z k) - z k‖ ^ 2 ≤
      ‖z 0 - zs‖ ^ 2 / (τ * ((k : ℝ) + 1))) ∧
    (fun k : ℕ => ‖TPRS Pf Pg (z k) - z k‖ ^ 2) =o[Filter.atTop]
      (fun k : ℕ => 1 / (τ * ((k : ℝ) + 1))) := by sorry

end RelaxedPRS.StrongCvx
