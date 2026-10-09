-- Prove2me | Theorems.Thm_WassFSG_Conc_lemma_5
-- name    : WassFSG.Conc.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T09:49:34.33448+00:00
-- url     : https://prove2.me/theorems/060ad616-0260-431c-8cfb-aefb2fb7eada
-- title:
--   Lemma 5 — concentration of F : Z^n → ℝ under T_p(τ): P(F > ε) ≤ exp(−n𝒥(ε;F)²/τ) and F ≤ ℛ(√(τt/n); F) w.p. ≥ 1 − e^{−t}
-- statement:
--   Let $\mathcal Z$ be a separable Banach space, $p\in[1,2]$, $\tau>0$, $n\ge1$, and let $\mathbb P_{\rm true}$ satisfy $T_p(\tau)$. Write $\mathbb P_\otimes$, $\mathbb E_\otimes$ for the $n$-fold product of $\mathbb P_{\rm true}$ on $\mathcal Z^n$ and $\mathsf d_p(z,\tilde z)^p=\sum_{i=1}^n\|z_i-\tilde z_i\|^p$. Let $F:\mathcal Z^n\to\mathbb R$ be measurable and $\mathbb P_\otimes$-integrable with $\mathbb E_\otimes[F]=0$, and suppose there are $M,L>0$ and $z_0\in\mathcal Z^n$ with
--   $$F(\tilde z)\le M+\frac Ln\,\mathsf d_p(\tilde z,z_0)^p\qquad\forall\tilde z\in\mathcal Z^n.$$
--   With the functionals $\mathcal J(\cdot;F)$ and $\mathcal R(\cdot;F)$ of the definitions module (the $\max(0,\cdot)$ reading of $\mathcal J^p$; $\mathcal R$ an infimum over $\lambda\ge0$):
--
--   1. for every $\varepsilon>0$,
--   $$\mathbb P_\otimes\{F(z)>\varepsilon\}\le\exp\big(-n\,\mathcal J(\varepsilon;F)^2/\tau\big);$$
--   2. for every $t>0$, with probability at least $1-e^{-t}$,
--   $$F(z)\le\mathcal R\Big(\sqrt{\tfrac{\tau t}{n}};F\Big).$$
--
--   This is the general concentration inequality behind Theorem 1, which is its specialization to $F(z)=\mathbb E_{\mathbb P_{\rm true}}[f]-\frac1n\sum_i f(z_i)$.
--
--   **Formalization Note** "With probability at least $1-e^{-t}$" is the bound $\mathbb P_\otimes(\text{bad set})\le e^{-t}$, where $\mathbb P_\otimes$ of an arbitrary set is its outer measure, so no measurability of the event is needed. The tail bound is $0$ when $\mathcal J(\varepsilon;F)=+\infty$. Since $\mathcal R\ge0$, the event $F(z)\le\mathcal R$ is written as $\max(F(z),0)\le\mathcal R$ in $[0,\infty]$, which is the same event and is trivially true when $\mathcal R=+\infty$. The printed "min" in $\mathcal R$ is read as an infimum and the printed codomain $\mathbb R_+$ of $\mathcal J$ as $\max(0,\cdot)$ (the supremum can be negative). $n\ge1$, measurability of $F$ (implicit in $\mathbb E_\otimes[F]=0$) and a complete separable Borel $\mathcal Z$ are standing assumptions.
-- source:
--   Gao, Finite-Sample Guarantees for Wasserstein Distributionally Robust Optimization: Breaking the Curse of Dimensionality, arXiv:2009.04382, Lemma 5, p. 21

import Mathlib
import Definitions.Def_WassFSG_Conc_Setting

namespace WassFSG.Conc

open MeasureTheory
open scoped ENNReal

/-- Lemma 5 (p. 21): concentration for a general `F : Z^n → ℝ` with `E_⊗[F] = 0` and the growth bound
`F(z̃) ≤ M + (L/n) d_p(z̃, z₀)^p`, when `P_true` satisfies `T_p(τ)`, `p ∈ [1, 2]`. -/
theorem lemma_5 {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]
    [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
    (n : ℕ) (hn : 0 < n) (p τ : ℝ) (hp1 : 1 ≤ p) (hp2 : p ≤ 2) (hτ : 0 < τ)
    (Ptrue : Measure Z) (hT : Tp p τ Ptrue)
    (F : (Fin n → Z) → ℝ) (hF : Measurable F)
    (hFint : Integrable F (Measure.pi fun _ : Fin n => Ptrue))
    (hF0 : ∫ z, F z ∂(Measure.pi fun _ : Fin n => Ptrue) = 0)
    (M L : ℝ) (hM : 0 < M) (hL : 0 < L) (z0 : Fin n → Z)
    (hgrowth : ∀ zt : Fin n → Z, F zt ≤ M + (L / (n : ℝ)) * dpPow p zt z0) :
    (∀ ε : ℝ, 0 < ε →
      Measure.pi (fun _ : Fin n => Ptrue) {z | ε < F z} ≤ expRate n τ p (Jpow n p Ptrue F ε)) ∧
    (∀ t : ℝ, 0 < t →
      Measure.pi (fun _ : Fin n => Ptrue)
          {z | ¬ (ENNReal.ofReal (F z) ≤ calR n p Ptrue F (Real.sqrt (τ * t / (n : ℝ))))}
        ≤ ENNReal.ofReal (Real.exp (-t))) := by sorry

end WassFSG.Conc
