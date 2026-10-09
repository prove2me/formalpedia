-- Prove2me | Theorems.Thm_WassFSG_Conc_corollary_1_p1
-- name    : WassFSG.Conc.corollary_1_p1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T09:49:53.596834+00:00
-- url     : https://prove2.me/theorems/33b4b3f2-4a5c-4a21-b3c7-798d70c3908a
-- title:
--   Corollary 1 (p = 1) — under T_1(τ) and Assumption 1(I), E f ≤ E_{P_n} f + √(τt/n)‖f‖_Lip w.p. ≥ 1 − e^{−t}
-- statement:
--   Let $\mathcal Z$ be a separable Banach space, and let $\mathbb P_{\rm true}$ satisfy $T_1(\tau)$ for some $\tau>0$. Let $\mathcal F$ be a class of losses satisfying Assumption 1(I): there is $\gamma_1>0$ such that for every $f\in\mathcal F$,
--   $$f(\tilde z)-f(z)\le\gamma_1\|\tilde z-z\|\qquad\forall z,\tilde z\in\mathcal Z.$$
--   Let $f\in\mathcal F$, $n\ge1$ and $t>0$. Then, with probability at least $1-e^{-t}$ over an i.i.d. sample of size $n$ from $\mathbb P_{\rm true}$,
--   $$\mathbb E_{\mathbb P_{\rm true}}[f]\le\mathbb E_{\mathbb P_n}[f]+\sqrt{\frac{\tau t}{n}}\cdot\|f\|_{\rm Lip},$$
--   where $\|f\|_{\rm Lip}=\sup_{z\ne z'}|f(z')-f(z)|/\|z'-z\|$.
--
--   This is the case $p=1$ of the variation-regularization corollary of Theorem 1: the deviation of the empirical loss is controlled by the Lipschitz norm of the loss.
--
--   **Formalization Note** "With probability at least $1-e^{-t}$" bounds the outer measure of the bad set by $e^{-t}$. Integrability of $f$ under $\mathbb P_{\rm true}$ follows from the Lipschitz bound and $\mathbb P_{\rm true}\in\mathcal P_1(\mathcal Z)$, and is not assumed. $n\ge1$ and a complete separable Borel $\mathcal Z$ are standing assumptions.
-- source:
--   Gao, Finite-Sample Guarantees for Wasserstein Distributionally Robust Optimization: Breaking the Curse of Dimensionality, arXiv:2009.04382, Corollary 1 (case p = 1), p. 7; Assumption 1(I), p. 5

import Mathlib
import Definitions.Def_WassFSG_Conc_Setting

namespace WassFSG.Conc

open MeasureTheory
open scoped ENNReal

/-- Corollary 1 (Variation regularization, p. 7), case `p = 1` under Assumption 1(I) (p. 5). -/
theorem corollary_1_p1 {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]
    [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
    (τ : ℝ) (hτ : 0 < τ) (Ptrue : Measure Z) (hT : Tp 1 τ Ptrue)
    (F : Set (Z → ℝ)) (γ₁ : ℝ) (hγ₁ : 0 < γ₁)
    (hA1 : ∀ g ∈ F, ∀ z zt : Z, g zt - g z ≤ γ₁ * ‖zt - z‖)
    (f : Z → ℝ) (hfF : f ∈ F) (n : ℕ) (hn : 0 < n) (t : ℝ) (ht : 0 < t) :
    Measure.pi (fun _ : Fin n => Ptrue)
        {z | ¬ (∫ x, f x ∂Ptrue ≤ empMean f z + Real.sqrt (τ * t / (n : ℝ)) * lipNorm f)}
      ≤ ENNReal.ofReal (Real.exp (-t)) := by sorry

end WassFSG.Conc
