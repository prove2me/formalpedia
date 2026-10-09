-- Prove2me | Theorems.Thm_ShortWDRODual_Tight_supFn_lsc
-- name    : ShortWDRODual.Tight.supFn_lsc
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T06:31:29.655994+00:00
-- url     : https://prove2.me/theorems/c68a423c-d28d-4ea8-80bf-b8546ce8b7dc
-- title:
--   Proof of Proposition 2, p. ec4 — Φ(x̂) = sup_x f(x) − λd(x̂, x)^p is lower semicontinuous and Borel measurable
-- statement:
--   Let $(\mathcal X,d)$ be a metric space with its Borel $\sigma$-algebra, $f:\mathcal X\to\mathbb R$ any function, $p\ge 1$ and $\lambda\ge 0$. Put $\varphi(\widehat x,x)=f(x)-\lambda d(\widehat x,x)^p$ and
--   $$\Phi(\widehat x)=\sup_{x\in\mathcal X}\big(f(x)-\lambda\,d(\widehat x,x)^p\big)\in\mathbb R\cup\{+\infty\}.$$
--   Then $\Phi$ is lower semicontinuous on $\mathcal X$, and hence Borel measurable.
--
--   This is the first step of the proof of Proposition 2: it makes $\Phi$ measurable even when $f$ is not, so that $\mathbb E_{\widehat{\mathbb P}}[\Phi]$ is an honest integral.
--
--   **Formalization Note** $\Phi$ takes values in the extended reals `EReal` with the order topology. No measurability of $f$ is assumed.
-- source:
--   Zhang, Yang & Gao, A Short and General Duality Proof for Wasserstein Distributionally Robust Optimization, arXiv:2205.00362v4, proof of Proposition 2, p. ec4 (PDF p. 18), first sentence

import Mathlib
import Definitions.Def_ShortWDRODual_Tight_Setting

namespace ShortWDRODual.Tight

/-- Proof of Proposition 2, arXiv:2205.00362v4, p. ec4: `φ(x̂, x) = f(x) − λ d(x̂, x)^p` is
continuous in `x̂`, so `Φ(x̂) = sup_x φ(x̂, x)` is lower semicontinuous, and thus Borel
measurable. No measurability of `f` is needed. -/
theorem supFn_lsc {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (f : X → ℝ) (p : ℝ) (hp : 1 ≤ p) (lam : ℝ) (hlam : 0 ≤ lam) :
    LowerSemicontinuous (ShortWDRODual.Legendre.supFn (pWassIntegrand f lam p)) ∧
      Measurable (ShortWDRODual.Legendre.supFn (pWassIntegrand f lam p)) := by sorry

end ShortWDRODual.Tight
