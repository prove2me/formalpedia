-- Prove2me | Theorems.Thm_RenegingLD_MM1_lemma_4_4
-- name    : RenegingLD.MM1.lemma_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:16:12.103239+00:00
-- url     : https://prove2.me/theorems/74de1a16-f16d-45e5-b9b4-6bb9aa711f1a
-- title:
--   Lemma 4.4, p. 20 — L is convex on ℝ₊ × ℝ × ℝ₊ and I_T is convex on C_T
-- statement:
--   Let $\lambda\ge\mu>0$, $\theta>0$, $x_0\ge0$, $T>0$.
--
--   1. The local rate $L$ is convex on $\mathbb R_+\times\mathbb R\times\mathbb R_+$: for $(x,p,q),(x',p',q')$ with $x,q,x',q'\ge0$ and $a\in(0,1)$,
--   $$L\big(a(x,p,q)+(1-a)(x',p',q')\big)\le a\,L(x,p,q)+(1-a)\,L(x',p',q').$$
--   2. $I_T$ is convex on $\mathcal C_T$: for $(\xi_1,\zeta_1),(\xi_2,\zeta_2)\in\mathcal C_T$ and $a\in(0,1)$, the combination $a(\xi_1,\zeta_1)+(1-a)(\xi_2,\zeta_2)$ lies in $\mathcal C_T$ and
--   $$I_T\big(a(\xi_1,\zeta_1)+(1-a)(\xi_2,\zeta_2)\big)\le a\,I_T(\xi_1,\zeta_1)+(1-a)\,I_T(\xi_2,\zeta_2).$$
--
--   Convexity is what turns the first-order conditions of §5 into a global minimality statement (Lemma 5.7) and gives convexity of $\gamma\mapsto I^*_{\gamma,T}$ (Lemma 6.1).
--
--   **Formalization Note.** Values are in $[0,\infty]$, where convexity is meant with the usual conventions; $a\in(0,1)$ excludes $0\cdot\infty$. The membership of the combination in $\mathcal C_T$ is stated explicitly because "convex function on $\mathcal C_T$" presupposes that $\mathcal C_T$ is convex, and the paper uses it (proofs of Lemmas 5.7 and 6.1).
-- source:
--   Atar, Budhiraja, Dupuis & Wu, Large Deviations for the Single Server Queue and the Reneging Paradox, arXiv:1903.06870v2, p. 20, Lemma 4.4

import Mathlib
import Definitions.Def_RenegingLD_MM1_Variational

namespace RenegingLD.MM1

open MeasureTheory Filter Topology
open scoped ENNReal

theorem lemma_4_4 (lam mu θ : ℝ) (hlam : 0 < lam) (hmu : 0 < mu) (hθ : 0 < θ) (hlm : mu ≤ lam) (x0 T : ℝ) (hx0 : 0 ≤ x0) (hT : 0 < T) :
    (∀ x p q x' p' q' a : ℝ, 0 ≤ x → 0 ≤ q → 0 ≤ x' → 0 ≤ q' → a ∈ Set.Ioo (0 : ℝ) 1 →
      Lloc lam mu θ (a * x + (1 - a) * x') (a * p + (1 - a) * p') (a * q + (1 - a) * q') ≤
        ENNReal.ofReal a * Lloc lam mu θ x p q
          + ENNReal.ofReal (1 - a) * Lloc lam mu θ x' p' q') ∧
    (∀ ξ₁ ζ₁ ξ₂ ζ₂ : ℝ → ℝ, ∀ a ∈ Set.Ioo (0 : ℝ) 1,
      InCT x0 T ξ₁ ζ₁ → InCT x0 T ξ₂ ζ₂ →
      InCT x0 T (fun t => a * ξ₁ t + (1 - a) * ξ₂ t) (fun t => a * ζ₁ t + (1 - a) * ζ₂ t) ∧
      IT lam mu θ x0 T (fun t => a * ξ₁ t + (1 - a) * ξ₂ t)
          (fun t => a * ζ₁ t + (1 - a) * ζ₂ t) ≤
        ENNReal.ofReal a * IT lam mu θ x0 T ξ₁ ζ₁
          + ENNReal.ofReal (1 - a) * IT lam mu θ x0 T ξ₂ ζ₂) := by sorry

end RenegingLD.MM1
