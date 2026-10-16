-- Prove2me | Theorems.Thm_SubsetShrink_L1_f_case_a
-- name    : SubsetShrink.L1.f_case_a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T21:26:42.070988+00:00
-- url     : https://prove2.me/theorems/3bbaa5ac-556b-4386-8131-2af8cb0d3daf
-- title:
--   p. 43 — case (a) under F and its slow-rate consequence
-- statement:
--   On $\mathcal F$, the noise correlation for $u=\hat\beta_1-\beta$ is bounded either by the $\ell_1$ term or by the prediction-norm term in the maximum defining the event. In case (a), if $\lambda\ge(8+2\sqrt2)\sigma\sqrt{\log(2p)}$, then
--
--   $$\epsilon^\top X(\hat\beta_1-\beta)\le(4+\sqrt2)\sigma\sqrt{\log(2p)}\,\|\beta-\hat\beta_1\|_1\quad\Longrightarrow\quad\|f^*-X\hat\beta_1\|_2^2\le\|f^*-X\beta\|_2^2+2\lambda\|\beta\|_1.$$
--
--   The alternative is retained because it leads to the additive $\sigma^2\log(1/\delta_0)$ term in the second slow rate.
--
--   **Formalization Note** The case (b) norm uses $\hat\beta_1$; the printed page accidentally writes $\hat\beta_2$ there.
-- source:
--   Mazumder, Radchenko & Dedieu, Subset Selection with Shrinkage, arXiv:1708.03288v4, p. 43, case (a), proof B.6

import Mathlib
import Definitions.Def_SubsetShrink_L1_Model

namespace SubsetShrink.L1

/-- Case (a) in B.6, p. 43. The alternative uses βhat₁ in the norm;
the printed βhat₂ there is a subscript slip. -/
theorem f_case_a {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ)
    (fstar ε : Fin n → ℝ) (k : ℕ) (σ δ0 lam : ℝ)
    (βhat β : Fin p → ℝ)
    (hσ : 0 < σ) (hδ0 : 0 < δ0) (hδ1 : δ0 ≤ 1)
    (hp : 1 ≤ p) (hF : ε ∈ SubsetShrink.Events.F X σ δ0)
    (hbest : IsL1BestSubset X (fun i => fstar i + ε i) k lam βhat)
    (hβ : SubsetShrink.Events.l0 β ≤ k)
    (hlam : (8 + 2 * Real.sqrt 2) * σ *
      Real.sqrt (Real.log (2 * (p : ℝ))) ≤ lam) :
    (SubsetShrink.Events.dot ε (X.mulVec (βhat - β)) ≤
        (4 + Real.sqrt 2) * σ * Real.sqrt (Real.log (2 * (p : ℝ))) *
          SubsetShrink.Events.l1 (β - βhat) ∨
      SubsetShrink.Events.dot ε (X.mulVec (βhat - β)) ≤
        (4 + Real.sqrt 2) * σ * Real.sqrt (Real.log (1 / δ0)) *
          SubsetShrink.Events.l2 (X.mulVec (β - βhat))) ∧
    (SubsetShrink.Events.dot ε (X.mulVec (βhat - β)) ≤
        (4 + Real.sqrt 2) * σ * Real.sqrt (Real.log (2 * (p : ℝ))) *
          SubsetShrink.Events.l1 (β - βhat) →
      predictionError X fstar βhat ≤
        predictionError X fstar β + 2 * lam * SubsetShrink.Events.l1 β) := by sorry

end SubsetShrink.L1
