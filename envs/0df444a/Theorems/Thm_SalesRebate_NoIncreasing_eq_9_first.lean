-- Prove2me | Theorems.Thm_SalesRebate_NoIncreasing_eq_9_first
-- name    : SalesRebate.NoIncreasing.eq_9_first
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:03:12.747327+00:00
-- url     : https://prove2.me/theorems/6c11a489-1550-49d2-a3a2-e153cf8b80a5
-- title:
--   (9), first equality, p. 16 (PDF 16) — expected profit as an integral over valuations above the cutoff
-- statement:
--   Let $(\theta, \sigma_\theta, \sigma_\epsilon)$ be a valid model, $p$ a price, $c$ a cutoff, and $\hat r : \mathbb R \to [0,p]$ a measurable reward (as a function of the quality). Then the firm's expected profit (2) equals the integral, over valuations above the cutoff, of the net price expected by each buyer weighted by the ex-ante density $\psi(x) = \phi((\theta-x)/\sigma)/\sigma$ of valuations:
--   $$\mathbb E_v\Big[(p - \hat r(v))\,\Phi\Big(\frac{v-c}{\sigma_\epsilon}\Big)\Big] = \int_c^\infty \big(p - \mathbb E_{v\mid v_i = x}[\hat r(v)]\big)\,\psi(x)\,dx,$$
--   where $\mathbb E_{v\mid v_i = x}$ is the expectation under the posterior $N(\tau x + (1-\tau)\theta, \sigma_v^2)$.
--
--   The identity re-expresses the profit by conditioning on consumers' valuations rather than on the quality; no equilibrium property of $c$ is used.
--
--   **Formalization Note** The page takes $\hat r \in L^\infty(\mathbb R; [0,p])$ (problem (3), p. 10); measurability and the range $[0,p]$ are stated as hypotheses. $\int_c^\infty$ is the integral over the open half-line $(c, \infty)$.
-- source:
--   Ajorlou, Jadbabaie, Sales-Based Rebate Design, arXiv:1902.09646v4, p. 16, (9), first equality

import Mathlib
import Definitions.Def_BlackScholesModel_Core
import Definitions.Def_SalesRebate_NoIncreasing_Setting

namespace SalesRebate.NoIncreasing

open MeasureTheory ProbabilityTheory BlackScholesModel

theorem eq_9_first (M : Model) (hM : M.Valid) (p : ℝ) (rhat : ℝ → ℝ)
    (hmeas : Measurable rhat) (hbound : ∀ v, rhat v ∈ Set.Icc 0 p) (c : ℝ) :
    M.expectedProfit p rhat c = ∫ x in Set.Ioi c, (p - M.condReward rhat x) * M.psi x := by sorry

end SalesRebate.NoIncreasing
