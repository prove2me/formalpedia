-- Prove2me | Theorems.Thm_WassFSG_Conc_proposition_1
-- name    : WassFSG.Conc.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T09:50:30.763621+00:00
-- url     : https://prove2.me/theorems/e4444bca-91f3-48fe-8d63-30778e5c357d
-- title:
--   Proposition 1 — I_p inverts the Wasserstein regularizer: I_p(R_{P_true,p}(ρ; f); f) = ρ if λ_o > λ̲, ≥ ρ if λ_o = λ̲
-- statement:
--   Let $\mathcal Z$ be a nontrivial separable Banach space, $p\in[1,\infty)$, and $\mathbb P_{\rm true}\in\mathcal P_p(\mathcal Z)$. Let $f:\mathcal Z\to\mathbb R$ be measurable and $\mathbb P_{\rm true}$-integrable, and suppose there are $M,L\ge0$ with
--   $$f(z)\le M+L\|z\|^p\qquad\forall z\in\mathcal Z.$$
--   Let $\rho>0$, and let $\lambda_o>0$ be a minimizer over $\lambda\ge0$ of the dual objective of (1) at $\mathbb Q=\mathbb P_{\rm true}$,
--   $$D(\lambda)=\lambda\rho^p+\mathbb E_{z\sim\mathbb P_{\rm true}}\Big[\sup_{\tilde z\in\mathcal Z}\{f(\tilde z)-\lambda\|\tilde z-z\|^p\}\Big].$$
--   Set $\underline\lambda=\limsup_{\|z\|\to\infty}f(z)/\|z\|^p$. Then the Wasserstein regularizer $\mathcal R_{\mathbb P_{\rm true},p}(\rho;f)$ is a finite real number $r$, and
--   $$\mathcal I_p(r;f)\ \begin{cases}=\rho,&\text{if }\lambda_o>\underline\lambda,\\ \ge\rho,&\text{if }\lambda_o=\underline\lambda.\end{cases}$$
--
--   So, at least for small radii, $\mathcal I_p(\cdot;f)$ is the left inverse of $\rho\mapsto\mathcal R_{\mathbb P_{\rm true},p}(\rho;f)$; this is what turns the tail bound of Lemma 5 into the high-probability bound of Theorem 1.
--
--   **Formalization Note** The conclusion is stated for $p$-th powers: $\mathcal I_p(r;f)^p=\rho^p$, resp. $\ge\rho^p$. The paper's $\underline\lambda=\lim_{\|z\|\to\infty}f(z)/\|z\|^p$ is read as a $\limsup$ in $[-\infty,\infty]$ (the limit need not exist, e.g. $f(z)=\|z\|^p\sin^2\|z\|$; the cited duality result [40] uses the limsup growth rate). Three readings are added and disclosed: $\mathcal Z$ is nontrivial (on $\mathcal Z=\{0\}$ the limsup over an empty neighbourhood filter is $-\infty$ and the equality case would fail; the paper's $\|z\|\to\infty$ presupposes unbounded $\mathcal Z$); $f$ is $\mathbb P_{\rm true}$-integrable (the regularizer is a difference with $\mathbb E_{\mathbb P_{\rm true}}[f]$, a real number in the paper); and $\mathbb P_{\rm true}\in\mathcal P_p(\mathcal Z)$, which (1) presupposes. The existence of the real value $r$ is part of the conclusion, since the paper evaluates $\mathcal I_p$, defined on $\mathbb R_+$, at it. Expectations in $D$ and in the regularizer are extended integrals in $[-\infty,\infty]$.
-- source:
--   Gao, Finite-Sample Guarantees for Wasserstein Distributionally Robust Optimization: Breaking the Curse of Dimensionality, arXiv:2009.04382, Proposition 1, p. 6 (dual problem (1), p. 5)

import Mathlib
import Definitions.Def_WassFSG_Conc_Setting

namespace WassFSG.Conc

open MeasureTheory
open scoped ENNReal

/-- Proposition 1 (p. 6): with `λ̲ = limsup_{‖z‖→∞} f(z)/‖z‖^p` and a positive dual minimizer `λ_o` of (1)
at `Q = P_true`, the regularizer `R_{P_true,p}(ρ; f)` is a real number `r` with
`I_p(r; f) = ρ` if `λ_o > λ̲` and `I_p(r; f) ≥ ρ` if `λ_o = λ̲` (stated for `I_p^p` and `ρ^p`). -/
theorem proposition_1 {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]
    [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z] [Nontrivial Z]
    (p : ℝ) (hp : 1 ≤ p) (Ptrue : Measure Z) (hP : IsPp (momentP p) Ptrue)
    (f : Z → ℝ) (hf : Measurable f) (hfint : Integrable f Ptrue)
    (M L : ℝ) (hM : 0 ≤ M) (hL : 0 ≤ L) (hgrowth : ∀ z : Z, f z ≤ M + L * ‖z‖ ^ p)
    (ρ : ℝ) (hρ : 0 < ρ) (lamo : ℝ) (hmin : IsDualMinimizer p ρ Ptrue f lamo) (hpos : 0 < lamo) :
    ∃ r : ℝ, regularizer p ρ Ptrue f = (r : EReal) ∧
      (growthRate p f < (lamo : EReal) → Ipow p Ptrue f r = ENNReal.ofReal (ρ ^ p)) ∧
      (growthRate p f = (lamo : EReal) → ENNReal.ofReal (ρ ^ p) ≤ Ipow p Ptrue f r) := by sorry

end WassFSG.Conc
