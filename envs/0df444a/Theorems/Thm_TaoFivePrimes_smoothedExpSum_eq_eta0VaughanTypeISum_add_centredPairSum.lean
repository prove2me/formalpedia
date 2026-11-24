-- Prove2me | Theorems.Thm_TaoFivePrimes_smoothedExpSum_eq_eta0VaughanTypeISum_add_centredPairSum
-- name    : TaoFivePrimes.smoothedExpSum_eq_eta0VaughanTypeISum_add_centredPairSum
-- status  : Proved
-- author  : @andreaskapfer
-- created : 2026-09-21T08:12:43.791342+00:00
-- url     : https://prove2.me/theorems/8556af74-ab0e-48be-823f-e702efd33d4e
-- title:
--   Centred Vaughan decomposition against the Type I interface
-- statement:
--   ## Centred Vaughan decomposition of $S_{\eta_0,2}$ against the Type I interface
--
--   Let $x,\alpha\in\mathbb R$ and $U,V\ge 40$ with $U,V<x$, $UV\le x/4$, $x\le UV^2$. Write $S_{\eta_0,2}(x,\alpha)=\sum_n\Lambda(n)\mathbf 1_{(n,2)=1}\eta_0(n/x)e(\alpha n)$ and let $\mathrm{TypeI}_{\eta_0}(x,\alpha,U,V)$ be the platform's pointwise Type I part `TaoFivePrimes.eta0VaughanTypeISum`. Then
--
--   $$S_{\eta_0,2}(x,\alpha)\;=\;\mathrm{TypeI}_{\eta_0}(x,\alpha,U,V)\;+\;\sum_{d\ge 1}\sum_{w\ge 1}\mu(d)\,\mathbf 1_{U<d}\,\mathbf 1_{V<w}\,\mathbf 1_{(d,2)=(w,2)=1}\,g(w)\,\eta_0(dw/x)\,e(\alpha dw),$$
--
--   $$g(w)=\sum_{\substack{b\mid w\\ b>V}}\Lambda(b)-\tfrac12\log w,$$
--
--   with the inner sums unconditionally convergent (the support of $\eta_0$ makes the sum finite). This is Tao's Lemma 4.11 decomposition with the **centred** Type II coefficient, stated in the form in which each side only uses the Type I interface: the summand on the right is the centred leftover that remains after the Type II bilinear part `TaoFivePrimes.eta0VaughanBilinearSum` is reindexed, and $g$ is `TaoFivePrimes.theorem51Centered`.
--
--   It is the exact companion of the two other halves of the split: `TaoFivePrimes.eta0VaughanBilinearSum_eq_centredPairSum` identifies the double sum above with the platform's bilinear sum, and `TaoFivePrimes.theorem51TypeISum_le_theorem51TypeI` compares the Type I part with the Type I envelope.
-- source:
--   Terence Tao, "Every odd number greater than 1 is the sum of at most five primes", Math. Comp. 83 (2014) 997-1038; arXiv:1201.6656v4, Section 4, Lemma 4.11 (Vaughan's identity) with the centred Type II coefficient $g(w)=\sum_{b\mid w,b>V}\Lambda(b)-\tfrac12\log w$, applied at the start of Section 5.

import Mathlib
import Definitions.Def_TaoFivePrimes_TypeIEnvelopeInterfaces

theorem TaoFivePrimes.smoothedExpSum_eq_eta0VaughanTypeISum_add_centredPairSum
    (x alpha U V : ℝ) (hU : 40 ≤ U) (hV : 40 ≤ V)
    (hUx : U < x) (hVx : V < x)
    (hUVx : U * V ≤ x / 4) (hUV2 : x ≤ U * V ^ 2) :
    TaoFivePrimes.smoothedExpSum TaoFivePrimes.eta0 2 x alpha =
      TaoFivePrimes.eta0VaughanTypeISum x alpha U V +
      ∑' d : ℕ, ∑' w : ℕ,
          (if U < (d : ℝ) ∧ V < (w : ℝ) ∧ d.Coprime 2 ∧ w.Coprime 2 then
            ((ArithmeticFunction.moebius d : ℤ) : ℂ) *
              (((TaoFivePrimes.theorem51Centered V w : ℝ)) : ℂ) *
              TaoFivePrimes.expCircle (alpha * d * w) *
              ((TaoFivePrimes.eta0 ((d : ℝ) * (w : ℝ) / x) : ℝ) : ℂ)
          else 0) := by sorry
