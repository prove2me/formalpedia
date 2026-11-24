-- Prove2me | Theorems.Thm_TaoFivePrimes_theorem51_vaughan_split_centred_assembly
-- name    : TaoFivePrimes.theorem51_vaughan_split_centred_assembly
-- status  : Open
-- author  : @andreaskapfer
-- created : 2026-09-21T08:24:45.517624+00:00
-- url     : https://prove2.me/theorems/401c5a3a-444c-450b-818d-ca04af3e7790
-- title:
--   Centred Vaughan assembly: decomposition identity and Type I envelope comparison
-- statement:
--   ## Centred Vaughan assembly: decomposition identity and Type I envelope comparison
--
--   Let $x,\alpha\in\mathbb R$ and $U,V\ge 40$ with $U,V<x$, $UV\le x/4$, $x\le UV^2$. This statement is the conjunction of the two facts that remain for the centred Vaughan split `TaoFivePrimes.theorem51_vaughan_split`.
--
--   **(i) The centred decomposition identity.**
--
--   $$S_{\eta_0,2}(x,\alpha)\;=\;\mathrm{TypeI}_{\eta_0}(x,\alpha,U,V)\;+\;\sum_{d\ge 1}\sum_{w\ge 1}\mu(d)\,\mathbf 1_{U<d}\,\mathbf 1_{V<w}\,\mathbf 1_{(d,2)=(w,2)=1}\,g(w)\,\eta_0(dw/x)\,e(\alpha dw),$$
--
--   $$g(w)=\sum_{\substack{b\mid w\\ b>V}}\Lambda(b)-\tfrac12\log w ,$$
--
--   where the right-hand double sum is the normed quantity displayed in the statement (its support is finite because of $\eta_0$). This is the centring of the Type II coefficient in Tao's Lemma 4.11, isolated against the Type I interface: the half-logarithmic leftover is absorbed into the double sum over pairs $(d,w)$ with $d>U$, $w>V$.
--
--   **(ii) The Type I envelope comparison.** There are coefficients $c_d\in\mathbb C$, $|c_d|\le 1$ for odd $d\le UV$, with
--   $$\bigl\|\mathrm{TypeI}_{\eta_0}(x,\alpha,U,V)\bigr\|\;\le\;\sum_{\substack{d\le UV\\ d\ \mathrm{odd}}}\Bigl\|\sum_{n\ \mathrm{odd}}\bigl(\log n+c_d\log d\bigr)\,\eta_0(dn/x)\,e(\alpha dn)\Bigr\|\;=\;T_I(x,\alpha,U,V;c).$$
--   This is the comparison step charged to the Type I envelope; the half-logarithmic leftover produced by the centring is charged to the small divisor variable, with the leftover terms re-indexed by the complementary factor (Dirichlet hyperbola). The witness is explicit: for odd $d\le UV$ with $\mu(d)\ne0$ take $c_d$ to be the unimodular factor aligning $c_d\log d\sum_n\eta_0(dn/x)e(\alpha dn)$ against $\sum_n(\log n)\eta_0(dn/x)e(\alpha dn)$; the comparison is against the full interface envelope with free unimodular factors, not the per-$d$ restricted comparison, which fails on the overlap range $x/(4V)\le d\le UV$.
--
--   **Why the target follows.** The platform definition `TaoFivePrimes.theorem51TypeII` *is* the norm of the centred pair sum displayed in (i):
--   $$T_{II}(x,\alpha,U,V)=\Bigl\|\sum_{d,w}\mu(d)\mathbf 1_{U<d}\mathbf 1_{V<w}\mathbf 1_{(d,2)=(w,2)=1}g(w)\eta_0(dw/x)e(\alpha dw)\Bigr\|.$$
--   Given (i) and (ii), with $c$ from (ii),
--   $$\|S_{\eta_0,2}\|=\|\mathrm{TypeI}_{\eta_0}+C\|\le\|\mathrm{TypeI}_{\eta_0}\|+\|C\|\le T_I(c)+T_{II},$$
--   which is exactly the centred Vaughan split. The remaining work is precisely (i) and (ii); both are stated as separate problems (`TaoFivePrimes.smoothedExpSum_eq_eta0VaughanTypeISum_add_centredPairSum` and `TaoFivePrimes.eta0VaughanTypeISum_le_theorem51TypeI`), and this conjunction packages them so that the split itself follows by unfolding the definition of $T_{II}$ and the triangle inequality.
-- source:
--   Terence Tao, "Every odd number greater than 1 is the sum of at most five primes", Math. Comp. 83 (2014) 997-1038; arXiv:1201.6656v4, Section 4, Lemma 4.11 (centred Type II coefficient $g(w)=\sum_{b\mid w,b>V}\Lambda(b)-\tfrac12\log w$) and Section 5 immediately before (5.8) (Type I envelope). Specified for the platform definitions of `TaoFivePrimes.theorem51TypeII` and `TaoFivePrimes.theorem51TypeI`.

import Mathlib
import Definitions.Def_TaoFivePrimes_TypeIEnvelopeInterfaces

theorem TaoFivePrimes.theorem51_vaughan_split_centred_assembly
    (x alpha U V : ℝ) (hU : 40 ≤ U) (hV : 40 ≤ V)
    (hUx : U < x) (hVx : V < x)
    (hUVx : U * V ≤ x / 4) (hUV2 : x ≤ U * V ^ 2) :
    (TaoFivePrimes.smoothedExpSum TaoFivePrimes.eta0 2 x alpha =
      TaoFivePrimes.eta0VaughanTypeISum x alpha U V +
      ∑' d : ℕ, ∑' w : ℕ,
        (if U < (d : ℝ) ∧ V < (w : ℝ) ∧ d.Coprime 2 ∧ w.Coprime 2 then
          (ArithmeticFunction.moebius d : ℂ) * (TaoFivePrimes.theorem51Centered V w : ℂ) *
            TaoFivePrimes.expCircle (alpha * d * w) * (TaoFivePrimes.eta0 ((d : ℝ) * w / x) : ℂ)
        else 0)) ∧
    (∃ c : ℕ → ℂ,
      (∀ d ∈ TaoFivePrimes.theorem51Divisors U V, ‖c d‖ ≤ 1) ∧
      ‖TaoFivePrimes.eta0VaughanTypeISum x alpha U V‖ ≤
        TaoFivePrimes.theorem51TypeI x alpha U V c) := by sorry
