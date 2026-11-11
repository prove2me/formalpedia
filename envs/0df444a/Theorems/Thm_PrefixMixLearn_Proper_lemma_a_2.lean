-- Prove2me | Theorems.Thm_PrefixMixLearn_Proper_lemma_a_2
-- name    : PrefixMixLearn.Proper.lemma_a_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T19:46:29.195206+00:00
-- url     : https://prove2.me/theorems/2b74b37a-d633-4b1f-a894-79a17dc576cd
-- title:
--   Lemma A.2 — quadratic collapse of a balanced two-product mixture to its mean product
-- statement:
--   Let $0<\alpha<1/2$, $u=\alpha(1-\alpha)$, and $M=(1-w)Q_\nu+wQ_\mu\in\mathcal M_{2,\alpha,T}$ ($w\in[0,1]$, $\mu,\nu\in[\alpha,1-\alpha]^T$) with mean vector $m=(1-w)\nu+w\mu$. With $\rho(d)=\sqrt{(\sum_i d_i^2)^2-\sum_i d_i^4}$,
--   $$d_{TV}(M,Q_m)\le\frac{w(1-w)\,\rho(\mu-\nu)}{2\sqrt2\,u}\le\frac{w(1-w)}{2\sqrt2\,u}\|\mu-\nu\|_2^2.$$
--   No separation or weight lower bound is imposed. This is the collapse step: a mixture whose components are close in Euclidean distance is close in law to a single balanced product.
--
--   Differences from the source:
--   - encoding: M = (1 − w)Q_ν + wQ_μ ∈ M_{2,α,T} → the representation (w, ν, μ) with w ∈ [0,1], ν, μ ∈ [α,1−α]^T is given; reason: every element of the class has such a representation and the bound is stated in terms of it
--   - encoding: coordinates i = 1, …, T; laws on {0,1}^T → `Fin T`, coordinate i ↦ i.val + 1; laws are real functions on `Fin T → Bool` with `IsLaw`; reason: Lean convention; same statement
-- source:
--   Saravanan, Proper Agnostic Learning of Two Balanced Product Distributions from Prefix-Conditional Samples, STOC 2027 submission (manuscript sha256 9c359910…), p. 13 (PDF 15), Lemma A.2

import Mathlib
import Definitions.Def_PrefixMixLearn_Proper_Laws
import Definitions.Def_PrefixMixLearn_Proper_Geometry

namespace PrefixMixLearn.Proper

/-- Lemma A.2 (quadratic collapse to the mean product): for `M = (1 − w)Q_ν + wQ_μ ∈ M_{2,α,T}`
and its mean `m = (1 − w)ν + wμ`,
`d_TV(M, Q_m) ≤ w(1 − w)ρ(μ − ν)/(2√2 u) ≤ (w(1 − w)/(2√2 u)) ‖μ − ν‖₂²`. -/
theorem lemma_a_2 (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1 / 2) (T : ℕ) (w : ℝ) (ν μ : Fin T → ℝ)
    (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (hν : InBox α ν) (hμ : InBox α μ) :
    tv (mixLaw w ν μ) (prodLaw (fun i => (1 - w) * ν i + w * μ i)) ≤
        w * (1 - w) * rhoQuad (fun i => μ i - ν i) / (2 * Real.sqrt 2 * uOf α) ∧
      w * (1 - w) * rhoQuad (fun i => μ i - ν i) / (2 * Real.sqrt 2 * uOf α) ≤
        w * (1 - w) / (2 * Real.sqrt 2 * uOf α) * l2 (fun i => μ i - ν i) ^ 2 := by sorry

end PrefixMixLearn.Proper
