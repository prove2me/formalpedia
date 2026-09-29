-- Prove2me | Theorems.Thm_StochLinOpt_UpperBound_zStat_le
-- name    : StochLinOpt.UpperBound.zStat_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T20:32:08.329755+00:00
-- url     : https://prove2.me/theorems/0d0e28ef-f317-440a-acd5-042f1b5ee0e8
-- title:
--   Lemma 12 — growth of $Z_t=(\hat\mu_t-\mu)^\top A_t(\hat\mu_t-\mu)$
-- statement:
--   Let $D\subseteq\mathbb R^n$ contain the standard basis vectors $e_1,\dots,e_n$ and let $\mu\in\mathbb R^n$ satisfy $|\mu^\top y|\le1$ for all $y\in D$. Let $x_1,x_2,\dots\in\mathbb R^n$ and $\ell_1,\ell_2,\dots\in\mathbb R$ be arbitrary, with $A_t$, $\hat\mu_t$ as in Algorithm 3.1, $w_\tau=\sqrt{x_\tau^\top A_\tau^{-1}x_\tau}$, noise $\eta_\tau=\ell_\tau-\mu^\top x_\tau$ and $Z_t=(\hat\mu_t-\mu)^\top A_t(\hat\mu_t-\mu)$. Then for every $t$,
--
--   $$Z_t\le n+2\sum_{\tau=1}^{t-1}\eta_\tau\frac{x_\tau^\top(\hat\mu_\tau-\mu)}{1+w_\tau^2}+\sum_{\tau=1}^{t-1}\eta_\tau^2\frac{w_\tau^2}{1+w_\tau^2}.$$
--
--   This deterministic recursion reduces the confidence statement to controlling a martingale (the middle sum) and a variance-like term.
--
--   **Formalization Note** The statement is pathwise and holds for every sequence. The constant $n$ bounds $Z_1=\|\mu\|^2=\sum_j(\mu^\top e_j)^2$, which uses $e_j\in D$ (the paper's Section 5 coordinate choice) and $|\mu^\top e_j|\le1$. Rounds are indexed from $1$.
-- source:
--   Dani, Hayes, Kakade, Stochastic Linear Optimization under Bandit Feedback, COLT 2008, PDF p. 9, Lemma 12

import Mathlib
import Definitions.Def_StochLinOpt_UpperBound_confidenceBall2
import Definitions.Def_StochLinOpt_UpperBound_analysisQuantities

open Matrix

namespace StochLinOpt.UpperBound

theorem zStat_le {n : ℕ} (D : Set (Fin n → ℝ)) (μ : Fin n → ℝ)
    (x : ℕ → Fin n → ℝ) (ℓ : ℕ → ℝ)
    (hD_basis : ∀ i : Fin n, (Pi.single i (1 : ℝ) : Fin n → ℝ) ∈ D)
    (hμD : ∀ y ∈ D, |μ ⬝ᵥ y| ≤ 1) (t : ℕ) :
    zStat μ x ℓ t ≤ n
      + 2 * ∑ τ ∈ Finset.Ico 1 t,
          (ℓ τ - μ ⬝ᵥ x τ) * (x τ ⬝ᵥ (muHat x ℓ τ - μ)) / (1 + width x τ ^ 2)
      + ∑ τ ∈ Finset.Ico 1 t,
          (ℓ τ - μ ⬝ᵥ x τ) ^ 2 * width x τ ^ 2 / (1 + width x τ ^ 2) := by sorry

end StochLinOpt.UpperBound
