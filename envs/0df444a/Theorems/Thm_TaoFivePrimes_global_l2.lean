-- Prove2me | Theorems.Thm_TaoFivePrimes_global_l2
-- name    : TaoFivePrimes.global_l2
-- status  : Proved
-- author  : @Patrick
-- created : 2026-09-07T01:55:35.28475+00:00
-- url     : https://prove2.me/theorems/a2c8c3bf-e5c2-4b30-8c80-83dffbc10b50
-- title:
--   Lemma 4.5 — Global L² estimate for smoothed prime sums
-- statement:
--   Let $x\geq1$, let $q$ be a natural number, and let $\eta:\mathbb R\to\mathbb R$ vanish for $t>1$. Write $S_{\eta,q}$ for the smoothed von Mangoldt exponential sum with the restriction $\gcd(n,q)=1$, as in equation (4.1) of Tao's paper. With normalized Haar measure on $\mathbb R/\mathbb Z$, the function $|S_{\eta,q}(x,\cdot)|^2$ is integrable and
--
--   $$\int_{\mathbb R/\mathbb Z}|S_{\eta,q}(x,\alpha)|^2\,d\alpha\leq S_{\eta^2,q}(x,0)\log x.$$
--
--   The quantity on the right is real and nonnegative. This global mean-square bound is an input to the local mass estimates used in the circle-method proof of the five-primes theorem.
--
--   **Formalization Note** This form implies Tao's Lemma 4.5 and explicitly records integrability. It omits the unused Section 4 assumptions that $q\geq1$ and that $\eta$ is nonnegative, bounded, measurable, and zero on negative arguments. Only vanishing above one is needed here. The real part of $S_{\eta^2,q}(x,0)$ expresses the real-valued right-hand side in Lean.
-- source:
--   Terence Tao, Every odd number greater than 1 is the sum of at most five primes, https://arxiv.org/abs/1201.6656, Lemma 4.5 (Global L² estimate), using equation (4.1). Generalized by dropping unused standing hypotheses from Section 4 and recording integrability.

import Definitions.Def_TaoFivePrimes_SmoothedSum
open MeasureTheory TaoFivePrimes

theorem TaoFivePrimes.global_l2 (η : ℝ → ℝ) (q : ℕ) (x : ℝ)
    (hx : 1 ≤ x) (hη : ∀ t : ℝ, 1 < t → η t = 0) :
    Integrable (fun α : AddCircle (1 : ℝ) ↦ ‖smoothedSum η q x α‖ ^ 2)
      AddCircle.haarAddCircle ∧
    (∫ α : AddCircle (1 : ℝ), ‖smoothedSum η q x α‖ ^ 2 ∂AddCircle.haarAddCircle) ≤
      (smoothedSum (fun t ↦ (η t) ^ 2) q x 0).re * Real.log x := by sorry
