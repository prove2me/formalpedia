-- Prove2me | Theorems.Thm_WassFSG_Conc_theorem_1
-- name    : WassFSG.Conc.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T09:49:35.751255+00:00
-- url     : https://prove2.me/theorems/a41247c1-2919-4d44-9a9a-23171e728b8b
-- title:
--   Theorem 1 — variation-based concentration under T_p(τ): tail bound exp(−nI_p(ε;−f)²/τ) and E f ≤ E_{P_n} f + R_{P_true,p}(√(τt/n); −f)
-- statement:
--   Let $\mathcal Z$ be a separable Banach space, $p\in[1,2]$, and let $\mathbb P_{\rm true}$ satisfy the transportation-information inequality $T_p(\tau)$ for some $\tau>0$. Let $f:\mathcal Z\to\mathbb R$ be measurable and $\mathbb P_{\rm true}$-integrable, and assume there are $M,L>0$ with
--   $$f(z)\le M+L\|z\|^p\qquad\forall z\in\mathcal Z.$$
--   Let $n\ge1$, let $z=(z_1,\dots,z_n)$ be an i.i.d. sample from $\mathbb P_{\rm true}$ with law $\mathbb P_\otimes$, and let $\mathbb E_{\mathbb P_n}[f]=\frac1n\sum_{i=1}^n f(z_i)$. Then:
--
--   1. for every $\varepsilon>0$,
--   $$\mathbb P_\otimes\big\{\mathbb E_{\mathbb P_n}[f]-\mathbb E_{\mathbb P_{\rm true}}[f]<-\varepsilon\big\}\le\exp\big(-n\,\mathcal I_p(\varepsilon;-f)^2/\tau\big);$$
--   2. for every $t>0$, with probability at least $1-e^{-t}$,
--   $$\mathbb E_{\mathbb P_{\rm true}}[f]\le\mathbb E_{\mathbb P_n}[f]+\mathcal R_{\mathbb P_{\rm true},p}\Big(\sqrt{\tfrac{\tau t}{n}};-f\Big).\tag{2}$$
--
--   The decay rate of the large-deviation probability of the empirical loss is governed by $\mathcal I_p(\cdot;-f)$, the inverse of the Wasserstein regularizer, and the deviation itself is controlled by the regularizer at radius $\sqrt{\tau t/n}$, with no dependence on the dimension of $\mathcal Z$.
--
--   **Formalization Note** $\mathcal I_p(\varepsilon;-f)^2$ is $(\mathcal I_p^p)^{2/p}$ with $\mathcal I_p^p=\max(0,\sup_{t>0}\{\varepsilon t-\Phi_{-f}(t)\})\in[0,\infty]$, and the tail bound is $0$ when it is $+\infty$. The regularizer is valued in $[-\infty,\infty]$ and is computed with extended integrals; "with probability at least $1-e^{-t}$" bounds the outer measure of the bad set by $e^{-t}$. Added and disclosed: $f$ is measurable and $\mathbb P_{\rm true}$-integrable (both displays use $\mathbb E_{\mathbb P_{\rm true}}[f]$ as a number), $n\ge1$, and $\mathcal Z$ complete, separable and Borel. The growth hypothesis is kept as printed, an upper bound on $f$, although the proof (via Lemma 5) uses a growth bound on $-f$: if $-f$ admits no bound $-f\le M'+L'\|z\|^p$, then $\Phi_{-f}\equiv+\infty$, so the first bound is $1$, and $\mathcal R_{\mathbb P_{\rm true},p}(\rho;-f)=+\infty$ for $\rho>0$, so (2) holds trivially.
-- source:
--   Gao, Finite-Sample Guarantees for Wasserstein Distributionally Robust Optimization: Breaking the Curse of Dimensionality, arXiv:2009.04382, Theorem 1 and eq. (2), p. 7

import Mathlib
import Definitions.Def_WassFSG_Conc_Setting

namespace WassFSG.Conc

open MeasureTheory
open scoped ENNReal

/-- Theorem 1 (Variation-based concentration, p. 7). -/
theorem theorem_1 {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]
    [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
    (p τ : ℝ) (hp1 : 1 ≤ p) (hp2 : p ≤ 2) (hτ : 0 < τ)
    (Ptrue : Measure Z) (hT : Tp p τ Ptrue)
    (f : Z → ℝ) (hf : Measurable f) (hfint : Integrable f Ptrue)
    (M L : ℝ) (hM : 0 < M) (hL : 0 < L) (hgrowth : ∀ z : Z, f z ≤ M + L * ‖z‖ ^ p)
    (n : ℕ) (hn : 0 < n) :
    (∀ ε : ℝ, 0 < ε →
      Measure.pi (fun _ : Fin n => Ptrue) {z | empMean f z - ∫ x, f x ∂Ptrue < -ε}
        ≤ expRate n τ p (Ipow p Ptrue (fun x => -f x) ε)) ∧
    (∀ t : ℝ, 0 < t →
      Measure.pi (fun _ : Fin n => Ptrue)
          {z | ¬ (((∫ x, f x ∂Ptrue : ℝ) : EReal) ≤
              (empMean f z : EReal) +
                regularizer p (Real.sqrt (τ * t / (n : ℝ))) Ptrue (fun x => -f x))}
        ≤ ENNReal.ofReal (Real.exp (-t))) := by sorry

end WassFSG.Conc
