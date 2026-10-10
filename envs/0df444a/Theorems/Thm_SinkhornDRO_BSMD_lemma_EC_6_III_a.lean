-- Prove2me | Theorems.Thm_SinkhornDRO_BSMD_lemma_EC_6_III_a
-- name    : SinkhornDRO.BSMD.lemma_EC_6_III_a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T14:27:05.307202+00:00
-- url     : https://prove2.me/theorems/8d0ec05f-cb18-4bff-bef8-c2db6fdfb51d
-- title:
--   Lemma EC.6 (III), first part — E‖g^ℓ(θ, ζ^ℓ)‖₂² ≤ L_f² on Θ
-- statement:
--   Let $\Theta$ be closed and convex, $\lambda,\epsilon>0$, $\widehat{\mathbb P}$ a probability measure and $\mathbb Q$ a Markov kernel. Let the loss $f_\theta(z)$ be measurable in $z$, convex in $\theta$, and $L_f$-Lipschitz in $\theta$ (Assumption 2(I)–(II)), with a subgradient selector $\nabla_\theta f_\theta(z)$ measurable in $z$. Then for every level $\ell$,
--   $$\mathbb E\big[\|g^\ell(\theta,\zeta^\ell)\|_2^2\big]\le L_f^2\qquad\forall\theta\in\Theta,$$
--   and the integrand is integrable. Here $g^\ell=\nabla_\theta U_{1:2^\ell}$ is the chain-rule subgradient of (15) and $\zeta^\ell$ has the level-$\ell$ sampling law.
--
--   With Assumption EC.1 this gives the SG second-moment bound $\mathbb E\|v^{SG}(\theta)\|_*^2\le\mathfrak c^{-2}L_f^2$ used in Theorem 2(I).
--
--   **Formalization Note** Assumption 2(I) is listed as on the page; the selector hypothesis already implies it.
-- source:
--   Wang, Gao, Xie, Sinkhorn Distributionally Robust Optimization, arXiv:2109.11926v5, p. ec19, Lemma EC.6 (III), first display

import Mathlib
import Definitions.Def_SinkhornDRO_BSMD_Objective
import Definitions.Def_SinkhornDRO_BSMD_Estimators

open MeasureTheory ProbabilityTheory

namespace SinkhornDRO.BSMD

/-- Lemma EC.6 (III), first part (Wang–Gao–Xie, arXiv:2109.11926v5, p. ec19): under
Assumption 2(II), `E[‖g^ℓ(θ, ζ^ℓ)‖₂²] ≤ L_f²` for every `θ ∈ Θ`, where `g^ℓ` is the chain-rule
subgradient of `U_{1:2^ℓ}` built from a subgradient selector `sg` of the loss and `ζ^ℓ` has the
level-`ℓ` sampling law. -/
theorem lemma_EC_6_III_a {d : ℕ} {Z : Type*} [MeasurableSpace Z]
    (Θ : Set (Param d)) (hΘc : IsClosed Θ) (hΘv : Convex ℝ Θ)
    (P : Measure Z) [IsProbabilityMeasure P] (Q : Kernel Z Z) [IsMarkovKernel Q]
    (lam eps : ℝ) (hlam : 0 < lam) (heps : 0 < eps)
    (f : Param d → Z → ℝ) (hf_meas : ∀ θ, Measurable (f θ))
    (Lf : ℝ) (hA2I : Asm2Convex f) (hA2II : Asm2Lipschitz f Lf)
    (sg : Param d → Z → Param d) (hsg : IsSubgradSel f sg) (hsg_meas : ∀ θ, Measurable (sg θ))
    (ℓ : ℕ) :
    ∀ θ ∈ Θ,
      Integrable (fun ζ : Z × (Fin (2 ^ ℓ) → Z) => ‖levelg lam eps f sg ℓ θ ζ.2‖ ^ 2)
          (levelLaw P Q (2 ^ ℓ)) ∧
        ∫ ζ, ‖levelg lam eps f sg ℓ θ ζ.2‖ ^ 2 ∂(levelLaw P Q (2 ^ ℓ)) ≤ Lf ^ 2 := by sorry

end SinkhornDRO.BSMD
