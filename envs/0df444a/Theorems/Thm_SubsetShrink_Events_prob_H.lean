-- Prove2me | Theorems.Thm_SubsetShrink_Events_prob_H
-- name    : SubsetShrink.Events.prob_H
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T19:31:20.797402+00:00
-- url     : https://prove2.me/theorems/bf5e6157-89eb-4507-8496-725ea3526021
-- title:
--   Theorem 1 (𝓗 part), p. 13; B.1, p. 38 — P(‖X⊤ϵ‖_∞ ≤ σ√(2 log 2p) + σ√(2 log(1/δ₀))) ≥ 1 − δ₀
-- statement:
--   Let $p\ge1$, let $X\in\mathbb R^{n\times p}$ have columns of unit Euclidean norm, let $\sigma>0$ and $\delta_0\in(0,1]$, and let $\epsilon$ have independent $N(0,\sigma^2)$ coordinates. Then the event
--   $$\mathcal H = \bigl\{\|X^\top\epsilon\|_\infty \le \sigma\sqrt{2\log(2p)}+\sigma\sqrt{2\log(1/\delta_0)}\bigr\}$$
--   is measurable and
--   $$\mathbb P(\mathcal H)\ge1-\delta_0 .$$
--
--   This is the maximal inequality for the $p$ Gaussian variables $X_j^\top\epsilon\sim N(0,\sigma^2)$; it is used for the $\ell_1$-regularized estimator (Theorem 3).
--
--   **Formalization Note** $\|X^\top\epsilon\|_\infty$ is the explicit maximum of $|\sum_i X_{ij}\epsilon_i|$ over $j$. The probability space is $\mathbb R^n$ with the law $N(0,\sigma^2)^{\otimes n}$. The hypothesis $p\ge1$ is the "$s\in[p]$" of Theorem 1.
-- source:
--   Mazumder, Radchenko & Dedieu, Subset Selection with Shrinkage, arXiv:1708.03288v4, p. 13, Theorem 1 (P(H) ≥ 1 − δ0); proof B.1, p. 38

import Mathlib
import Definitions.Def_SubsetShrink_Events_Model

open MeasureTheory ProbabilityTheory

namespace SubsetShrink.Events
theorem prob_H {n p : ℕ} (hp : 1 ≤ p) (X : Matrix (Fin n) (Fin p) ℝ) (hX : UnitCols X)
    (σ : ℝ) (hσ : 0 < σ) (δ0 : ℝ) (hδ0 : 0 < δ0) (hδ1 : δ0 ≤ 1) :
    MeasurableSet (H X σ δ0) ∧ 1 - δ0 ≤ (noiseLaw n σ (H X σ δ0)).toReal := by sorry
end SubsetShrink.Events
