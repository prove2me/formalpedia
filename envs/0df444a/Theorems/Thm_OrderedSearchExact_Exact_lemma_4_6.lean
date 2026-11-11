-- Prove2me | Theorems.Thm_OrderedSearchExact_Exact_lemma_4_6
-- name    : OrderedSearchExact.Exact.lemma_4_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:05:48.760765+00:00
-- url     : https://prove2.me/theorems/6adca9c0-357a-4177-9619-ebf2280ffe5e
-- title:
--   Lemma 4.6 — continuum certificate gives finite progress
-- statement:
--   Let $h$ be any compactly supported probability density, $d>0$, $0<\rho<1$, and $M>0$. Suppose
--
--   $$b_h(x)-b_h(x-d)\le2\rho\sqrt{a_h(x)a_h(x-d)}\quad(x\in\mathbb R),\qquad \tanh(M/2)>\rho^2.$$
--
--   For a positive center $\alpha$, set $\beta=e^d\alpha$ and suppose both physical-rate mixtures are at least $M$ almost surely. Then, for every integer $n\ge2$, both $q_{S_{\beta e^Y}+A_{\alpha e^Y}}$ and $q_{S_{\alpha e^Y}+A_{\beta e^Y}}$ are nonnegative at every angle. This is an exact statement about finite Laurent polynomials, with no large-$n$ approximation.
--
--   Differences from the source:
--   - encoding: normalized real symmetric Laurent polynomials of degree less than n → real coefficient vectors indexed by Fin (n-1), with frequency i+1 and evaluation on every real angle; reason: this bijects the source coefficients, preserves the constant coefficient 1, and includes all points of the unit circle
--   - encoding: expectations under a compactly supported probability density → full Lebesgue integrals against a measurable nonnegative density of mass one and almost-sure compact support; reason: the same density class is used; bounded coefficient kernels are integrable against every such density
--   - encoding: rates in [0,infinity], with limiting endpoints → ENNReal rates with explicit zero and infinity branches; reason: the extended supremum never defaults to a finite real value; the endpoint polynomials are the prescribed limits
-- source:
--   Joseph Carolan, Andrew Childs, STOC 2027 submission #1443 (October 2026), Lemma 4.6, p.17 (PDF p.17); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1443.pdf; sha256 8bb6cbb4037a439039875fd77a9f212e2c0f90a6e87f0c4c690230223813da44

import Definitions.Def_OrderedSearchExact_Exact_Analysis

namespace OrderedSearchExact.Exact

theorem lemma_4_6 (h : ℝ → ℝ) (hh : IsDensity h) (d ρ M : ℝ)
    (hd : 0 < d) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hc : Certificate h d ρ)
    (hM : 0 < M) (ht : ρ ^ 2 < Real.tanh (M / 2))
    (α : Rate) (hα : 0 < α)
    (ha : AlmostSure h (fun y => ENNReal.ofReal M ≤ physicalRate α y))
    (hb : AlmostSure h (fun y => ENNReal.ofReal M ≤
      physicalRate (ENNReal.ofReal (Real.exp d) * α) y)) :
    ∀ n : ℕ, 2 ≤ n →
      Nonnegative (hybrid n h (ENNReal.ofReal (Real.exp d) * α) α) ∧
      Nonnegative (hybrid n h α (ENNReal.ofReal (Real.exp d) * α)) := by sorry

end OrderedSearchExact.Exact
