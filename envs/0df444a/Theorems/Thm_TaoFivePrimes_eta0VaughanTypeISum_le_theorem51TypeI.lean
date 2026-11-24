-- Prove2me | Theorems.Thm_TaoFivePrimes_eta0VaughanTypeISum_le_theorem51TypeI
-- name    : TaoFivePrimes.eta0VaughanTypeISum_le_theorem51TypeI
-- status  : Open
-- author  : @andreaskapfer
-- created : 2026-09-21T08:12:44.02977+00:00
-- url     : https://prove2.me/theorems/62275301-9a4a-4c22-8111-2da44b4cb2f2
-- title:
--   Type I envelope comparison for the centred Vaughan Type I part
-- statement:
--   ## Type I envelope comparison for the centred Vaughan Type I part
--
--   Let $x,\alpha\in\mathbb R$ and $U,V\ge 40$ with $U,V<x$, $UV\le x/4$, $x\le UV^2$. There are coefficients $c_d\in\mathbb C$ with $|c_d|\le 1$ for every odd $d\le UV$ such that
--
--   $$\bigl\|\mathrm{TypeI}_{\eta_0}(x,\alpha,U,V)\bigr\|\;\le\;\sum_{\substack{d\le UV\\ d\ \mathrm{odd}}}\Bigl\|\sum_{n\ \mathrm{odd}}\bigl(\log n+c_d\log d\bigr)\,\eta_0(dn/x)\,e(\alpha dn)\Bigr\|\;=\;T_I(x,\alpha,U,V;c),$$
--
--   where the left side is the platform's `TaoFivePrimes.eta0VaughanTypeISum`. This is the comparison step charged to the Type I envelope in Tao's Lemma 4.11: the half-logarithmic leftover produced by the centring of the Type II coefficient has to be dominated by sums of the form $\sum_{d\le UV}|\sum_n(\log n)F(dn)|$ carried by the small divisor variable, with the leftover terms re-indexed by the complementary factor (Dirichlet hyperbola). The witness is explicit: for each odd $d\le UV$ with $\mu(d)\ne 0$ take $c_d$ equal to the unimodular factor aligning $c_d\log d\sum_n\eta_0(dn/x)e(\alpha dn)$ against $\sum_n(\log n)\eta_0(dn/x)e(\alpha dn)$, and $c_d=0$ if $\mu(d)=0$. The comparison is against the full interface envelope $T_I(c)$ with the free unimodular factors $c_d$, not the per-$d$ restricted comparison, which fails on the overlap range $x/(4V)\le d\le UV$.
-- source:
--   Terence Tao, arXiv:1201.6656v4, Section 4, Lemma 4.11 and the absorption of the half-logarithmic leftover in its proof; the Type I envelope as used in Section 5 preceding (5.8), https://arxiv.org/html/1201.6656v4#S5.

import Mathlib
import Definitions.Def_TaoFivePrimes_TypeIEnvelopeInterfaces

theorem TaoFivePrimes.eta0VaughanTypeISum_le_theorem51TypeI
    (x alpha U V : ℝ) (hU : 40 ≤ U) (hV : 40 ≤ V)
    (hUx : U < x) (hVx : V < x)
    (hUVx : U * V ≤ x / 4) (hUV2 : x ≤ U * V ^ 2) :
    ∃ c : ℕ → ℂ,
      (∀ d ∈ TaoFivePrimes.theorem51Divisors U V, ‖c d‖ ≤ 1) ∧
      ‖TaoFivePrimes.eta0VaughanTypeISum x alpha U V‖ ≤
        TaoFivePrimes.theorem51TypeI x alpha U V c := by sorry
