-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P32_fidelity_bounds_affine_positive
-- name    : QAlgorithms.Papers.Independent.Dependency50.P32.fidelity_bounds_affine_positive
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T14:55:40.939663+00:00
-- url     : https://prove2.me/theorems/58810f42-9170-467d-950a-1693560d74cd
-- title:
--   Theorem 6 (D2): positive-parameter affine fidelity bounds
-- statement:
--   All Hilbert spaces have strictly positive finite dimension. For each channel type, let $\mathcal O_{\rm all}$ be the closed convex physically allowed family of CPTP maps, with a nonempty closed convex free subset $\mathcal O$; primes indicate the output fibre. Let $\mathbb S$ be the maximal family of deterministic physical superchannels preserving both the allowed structures and the free fibres. Write $F$ for squared Uhlmann fidelity minimized over normalized reference-assisted input states, with an input-sized reference.
--
--   The multiplicative quantities $R_s$, $R_{\max}$, $R_H^\eta$, and $R_{\min}$ are standard robustness, generalized robustness, hypothesis-testing resource, and zero-error ordinary testing resource. Their affine versions use the affine saddle/equal-overlap domains; affine min-resource uses support-projector overlaps and is distinct from zero-error affine testing. Smoothing means the extended infimum over physically allowed channels with fidelity at least $1-\eta$; tolerances at least one give the whole allowed fibre. Unless specified otherwise, smoothing errors lie in $[0,1]$.
--
--   Suppose $N$ preserves reference-assisted purity and explicitly assume $R_{\min,\operatorname{aff}(\mathcal O')}(N)>0$. With $F_*(E\to N)$ denoting the attained maximum free conversion fidelity,
--   $$
--   G_{\operatorname{aff}(\mathcal O)}(E;R_{\min,\operatorname{aff}(\mathcal O')}(N))\ge F_*(E\to N)\ge G_{\operatorname{aff}(\mathcal O)}(E;R_{\max,\mathcal O'}(N)).
--   $$
--   Infinite resource parameters are represented by reciprocal threshold zero. Positivity restricts this statement to the domain where the printed gauge is defined.
--
--   The unrestricted numbered theorem remains deferred because the source permits affine min-resource zero without defining the gauge at zero.
-- source:
--   One-Shot Manipulation of Dynamical Quantum Resources, arXiv:2012.02215v3, PDF p. 12, Theorem 6 (D2): positive-parameter affine fidelity bounds

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P32

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Dependency50.P32

open QAlgorithms.Papers.Independent.Information100.P07 (support)

/-- Theorem 6 (D2), PDF pp.12-13, restricted to its well-defined POSITIVE
parameter domain. The unrestricted printed zero endpoint remains in HARD.md.
Source-scope correction: printed p.2 assumes only closed convex free fibres;
changed to the additional explicit ClosedConvexAllowed hypothesis, because
allowed-channel mixing and quantitative optimizer selection are used in the
conversion construction. The unrestricted allowed-subset case is not claimed. -/
theorem fidelity_bounds_affine_positive (O : ResourceTheory) (hO : Regular O) (hAllowed : ClosedConvexAllowed O) {p q : Port}
    (E : ChannelChoi p) (N : ChannelChoi q) (hE : E ∈ O.allowed p) (hN : N ∈ O.allowed q)
    (hpure : PureTarget N) (hpos : 0 < minimumAffine O N) :
    gaugeAffine O E ((maximal O N)⁻¹) ≤ bestFidelity O E N ∧
    bestFidelity O E N ≤ gaugeAffine O E ((minimumAffine O N)⁻¹) ∧
    ∃ Theta : ChannelChoi p →ₗ[ℂ] ChannelChoi q, FreeSuperchannel O Theta ∧
      ENNReal.ofReal (worstCaseFidelity (Theta E) N) = bestFidelity O E N := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P32

end
