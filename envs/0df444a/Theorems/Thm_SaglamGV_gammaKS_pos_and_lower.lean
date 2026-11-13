-- Prove2me | Theorems.Thm_SaglamGV_gammaKS_pos_and_lower
-- name    : SaglamGV.gammaKS_pos_and_lower
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:47:44.354205+00:00
-- url     : https://prove2.me/theorems/dbc9930d-d9fc-4212-9a3a-5b6908ab74ba
-- title:
--   $\gamma>0$ on $(0,1/2)$, $\gamma(\rho)=\frac\rho2\lg\frac1\rho+O(\rho)$, and $\gamma(\rho)\ge c_\eta\rho\lg\frac1\rho$
-- statement:
--   Let $\gamma(\rho)=-\frac\rho2\lg\rho-2(1-\rho)\lg(1-\rho)-1+(1-\frac{3\rho}2)\lg(2-3\rho)$. Then
--
--   1. $\gamma(\rho)>0$ for $0<\rho<1/2$;
--   2. $\gamma(\rho)=\frac\rho2\lg\frac1\rho+O(\rho)$ as $\rho\to0$: there are $C$ and $\delta>0$ with $|\gamma(\rho)-\frac\rho2\lg\frac1\rho|\le C\rho$ for $0<\rho<\delta$;
--   3. for every $\eta>0$ there is $c_\eta>0$ with
--   $$
--   \gamma(\rho)\ge c_\eta\,\rho\lg\frac1\rho\qquad(0<\rho\le\tfrac12-\eta).
--   $$
--
--   The lower bound gives the factor $2^{-c_\eta w\lg(n/w)}$ in the third-moment estimate of Lemma 3.1.
--
--   Differences from the source:
--   - encoding: O(ρ) as ρ → 0 → ∃ C, δ > 0 with |γ(ρ) − (ρ/2) lg(1/ρ)| ≤ Cρ on (0, δ); reason: the meaning of O(·) at 0
-- source:
--   M. Saglam, Linear codes exceeding the Gilbert–Varshamov bound, STOC 2027 submission manuscript (held version, sha256 ac6f2bba913aa15cfec8dda07a8e9e37b7186e145fef4719cb623dd04d15baa3), Appendix A, p.6 (γ positive on (0, 1/2); γ(ρ) = (ρ/2) lg(1/ρ) + O(ρ); γ(ρ) ≥ c_η ρ lg(1/ρ) for 0 < ρ ≤ 1/2 − η)

import Mathlib
import Definitions.Def_SaglamGV_Analytic

namespace SaglamGV

/-- Positivity and growth of $γ$ (M. Saglam, *Linear codes exceeding the Gilbert–Varshamov bound*, STOC 2027 submission manuscript (held version, sha256 ac6f2bba…), Appendix A, p.6: "It follows that γ is strictly positive on
(0, 1/2) and γ(ρ) = (ρ/2) lg(1/ρ) + O(ρ) (ρ → 0). Consequently, for every fixed η > 0, there is a
constant c_η > 0 such that γ(ρ) ≥ c_η ρ lg(1/ρ) (0 < ρ ≤ 1/2 − η)").

**Formalization Note** "$O(ρ)$ as $ρ → 0$" is $|γ(ρ) − (ρ/2)\lg(1/ρ)| ≤ Cρ$ on some $(0, δ)$. -/
theorem gammaKS_pos_and_lower :
    (∀ ρ : ℝ, 0 < ρ → ρ < 1 / 2 → 0 < gammaKS ρ) ∧
      (∃ C δ : ℝ, 0 < δ ∧ ∀ ρ : ℝ, 0 < ρ → ρ < δ →
        |gammaKS ρ - ρ / 2 * Real.logb 2 (1 / ρ)| ≤ C * ρ) ∧
      (∀ η : ℝ, 0 < η → ∃ c : ℝ, 0 < c ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 / 2 - η →
        c * ρ * Real.logb 2 (1 / ρ) ≤ gammaKS ρ) := by sorry

end SaglamGV
