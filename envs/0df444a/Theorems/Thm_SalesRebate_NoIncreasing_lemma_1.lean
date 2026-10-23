-- Prove2me | Theorems.Thm_SalesRebate_NoIncreasing_lemma_1
-- name    : SalesRebate.NoIncreasing.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:03:20.456012+00:00
-- url     : https://prove2.me/theorems/448defbb-46ea-47a0-bbef-5abc4c36a8f8
-- title:
--   Lemma 1, p. 16 (PDF 16) — at an equilibrium cutoff, profit beats the price-c no-reward profit iff E[r̂|vᵢ = c] > E[r̂|vᵢ ≥ c]
-- statement:
--   Let $(\theta, \sigma_\theta, \sigma_\epsilon)$ be a valid model, $p$ a price, $\hat r : \mathbb R \to [0,p]$ a measurable reward, and suppose the threshold strategy $a_i = \mathbf 1\{v_i > c\}$ is an equilibrium for $(p, \hat r)$ in the sense of (1). Write $r(x) = \mathbb E_{v\mid v_i = x}[\hat r(v)]$. Then
--   $$\mathbb E_v[\Pi(p, \hat r)] > \mathbb E_v[\Pi(c, 0)] \iff \mathbb E_v[\hat r(v)\mid v_i \ge c] < \mathbb E_v[\hat r(v) \mid v_i = c] = r(c),$$
--   where
--   $$\mathbb E_v[\hat r(v)\mid v_i \ge c] = \frac{\int_c^\infty r(x)\psi(x)\,dx}{\int_c^\infty \psi(x)\,dx}.$$
--
--   In words, the reward program beats the plain price $c$ exactly when the expected reward paid per purchase is below the reward expected by the indifferent consumer.
--
--   **Formalization Note** The denominator $\int_c^\infty \psi$ is the probability that a valuation exceeds $c$, which is positive for every real $c$, so the real division needs no guard. Measurability and the range $[0,p]$ of $\hat r$ come from $\hat r \in L^\infty(\mathbb R; [0,p])$ (p. 10). The equilibrium hypothesis is the full condition (1), as on the page.
-- source:
--   Ajorlou, Jadbabaie, Sales-Based Rebate Design, arXiv:1902.09646v4, p. 16, Lemma 1, (10)

import Mathlib
import Definitions.Def_BlackScholesModel_Core
import Definitions.Def_SalesRebate_NoIncreasing_Setting

namespace SalesRebate.NoIncreasing

open MeasureTheory ProbabilityTheory BlackScholesModel

theorem lemma_1 (M : Model) (hM : M.Valid) (p : ℝ) (rhat : ℝ → ℝ)
    (hmeas : Measurable rhat) (hbound : ∀ v, rhat v ∈ Set.Icc 0 p) (c : ℝ)
    (hc : M.IsEquilibriumCutoff p rhat c) :
    M.expectedProfit c (fun _ => 0) c < M.expectedProfit p rhat c ↔
      (∫ x in Set.Ioi c, M.condReward rhat x * M.psi x) / (∫ x in Set.Ioi c, M.psi x) <
        M.condReward rhat c := by sorry

end SalesRebate.NoIncreasing
