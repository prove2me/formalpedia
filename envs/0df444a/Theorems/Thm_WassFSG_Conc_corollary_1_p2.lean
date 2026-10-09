-- Prove2me | Theorems.Thm_WassFSG_Conc_corollary_1_p2
-- name    : WassFSG.Conc.corollary_1_p2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T09:49:42.051862+00:00
-- url     : https://prove2.me/theorems/748d0408-085b-4976-9508-8c67a66a6c47
-- title:
--   Corollary 1 (p = 2) — under T_2(τ) and Assumption 2, E f ≤ E_{P_n} f + √(τt/n)‖‖∇f‖_*‖_{P_true,2} + ħτt/n w.p. ≥ 1 − e^{−t}
-- statement:
--   Let $\mathcal Z$ be a separable Banach space with dual norm $\|\cdot\|_*$, and let $\mathbb P_{\rm true}$ satisfy $T_2(\tau)$ for some $\tau>0$. Let $\mathcal F$ be a class of losses satisfying Assumption 2: every $f\in\mathcal F$ is differentiable and there is $\hbar>0$ with
--   $$\|\nabla f(\tilde z)-\nabla f(z)\|_*\le\hbar\|\tilde z-z\|\qquad\forall\tilde z,z\in\mathcal Z,\ \forall f\in\mathcal F.$$
--   Let $f\in\mathcal F$, $n\ge1$ and $t>0$. Then, with probability at least $1-e^{-t}$ over an i.i.d. sample of size $n$ from $\mathbb P_{\rm true}$,
--   $$\mathbb E_{\mathbb P_{\rm true}}[f]\le\mathbb E_{\mathbb P_n}[f]+\sqrt{\frac{\tau t}{n}}\cdot\big\|\|\nabla f\|_*\big\|_{\mathbb P_{\rm true},2}+\frac{\hbar\tau t}{n},$$
--   where $\big\|\|\nabla f\|_*\big\|_{\mathbb P_{\rm true},2}=\big(\mathbb E_{\mathbb P_{\rm true}}[\|\nabla f(z)\|_*^2]\big)^{1/2}$.
--
--   This is the case $p=2$ of the variation-regularization corollary of Theorem 1: the deviation is controlled by the $L^2$ norm of the gradient, which is never larger than the Lipschitz norm.
--
--   **Formalization Note** $\nabla f(z)$ is the Fréchet derivative, a continuous linear functional on $\mathcal Z$, and $\|\cdot\|_*$ is its operator norm. "With probability at least $1-e^{-t}$" bounds the outer measure of the bad set by $e^{-t}$. Integrability of $f$ and of $\|\nabla f\|_*^2$ under $\mathbb P_{\rm true}$ follows from Assumption 2 and $\mathbb P_{\rm true}\in\mathcal P_2(\mathcal Z)$, and is not assumed. $n\ge1$ and a complete separable Borel $\mathcal Z$ are standing assumptions.
-- source:
--   Gao, Finite-Sample Guarantees for Wasserstein Distributionally Robust Optimization: Breaking the Curse of Dimensionality, arXiv:2009.04382, Corollary 1 (case p = 2), p. 7; Assumption 2, p. 5

import Mathlib
import Definitions.Def_WassFSG_Conc_Setting

namespace WassFSG.Conc

open MeasureTheory
open scoped ENNReal

/-- Corollary 1 (Variation regularization, p. 7), case `p = 2` under Assumption 2 (p. 5). -/
theorem corollary_1_p2 {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]
    [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
    (τ : ℝ) (hτ : 0 < τ) (Ptrue : Measure Z) (hT : Tp 2 τ Ptrue)
    (F : Set (Z → ℝ)) (hbar : ℝ) (hhbar : 0 < hbar)
    (hdiff : ∀ g ∈ F, Differentiable ℝ g)
    (hA2 : ∀ g ∈ F, ∀ zt z : Z, ‖fderiv ℝ g zt - fderiv ℝ g z‖ ≤ hbar * ‖zt - z‖)
    (f : Z → ℝ) (hfF : f ∈ F) (n : ℕ) (hn : 0 < n) (t : ℝ) (ht : 0 < t) :
    Measure.pi (fun _ : Fin n => Ptrue)
        {z | ¬ (∫ x, f x ∂Ptrue ≤ empMean f z +
            Real.sqrt (τ * t / (n : ℝ)) * Real.sqrt (∫ x, ‖fderiv ℝ f x‖ ^ 2 ∂Ptrue) +
              hbar * τ * t / (n : ℝ))}
      ≤ ENNReal.ofReal (Real.exp (-t)) := by sorry

end WassFSG.Conc
