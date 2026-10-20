-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P32_fidelity_bounds_ordinary
-- name    : QAlgorithms.Papers.Independent.Dependency50.P32.fidelity_bounds_ordinary
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T14:53:52.756076+00:00
-- url     : https://prove2.me/theorems/141d9413-ee7a-4148-b3e0-66ff37c96abd
-- title:
--   Theorem 6 (D1): ordinary fidelity bounds
-- statement:
--   All Hilbert spaces have strictly positive finite dimension. For each channel type, let $\mathcal O_{\rm all}$ be the closed convex physically allowed family of CPTP maps, with a nonempty closed convex free subset $\mathcal O$; primes indicate the output fibre. Let $\mathbb S$ be the maximal family of deterministic physical superchannels preserving both the allowed structures and the free fibres. Write $F$ for squared Uhlmann fidelity minimized over normalized reference-assisted input states, with an input-sized reference.
--
--   The multiplicative quantities $R_s$, $R_{\max}$, $R_H^\eta$, and $R_{\min}$ are standard robustness, generalized robustness, hypothesis-testing resource, and zero-error ordinary testing resource. Their affine versions use the affine saddle/equal-overlap domains; affine min-resource uses support-projector overlaps and is distinct from zero-error affine testing. Smoothing means the extended infimum over physically allowed channels with fidelity at least $1-\eta$; tolerances at least one give the whole allowed fibre. Unless specified otherwise, smoothing errors lie in $[0,1]$.
--
--   Suppose $N$ preserves reference-assisted purity and put $F_*(E\to N)=\max_{\Theta\in\mathbb S}F(\Theta(E),N)$. Then
--   $$
--   G_{\mathcal O}(E;R_{\min,\mathcal O'}(N))\ge F_*(E\to N)\ge G_{\mathcal O}(E;R_{s,\mathcal O'}(N)).
--   $$
--   An actual maximizing physical free superchannel exists. Each gauge is evaluated using the reciprocal of its resource parameter; an infinite parameter gives threshold zero, including the case $R_s(N)=\infty$.
--
--   This is the complete independently well-defined ordinary branch of Theorem 6, not a replacement for the deferred unrestricted affine branch.
-- source:
--   One-Shot Manipulation of Dynamical Quantum Resources, arXiv:2012.02215v3, PDF p. 12, Theorem 6 (D1): ordinary fidelity bounds

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P32

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Dependency50.P32

open QAlgorithms.Papers.Independent.Information100.P07 (support)

/-- Theorem 6 (D1), PDF pp.12-13: full ordinary two-sided bounds and an
attaining physical free superchannel. Infinity robustness gives threshold zero.
Source-scope correction: printed p.2 assumes only closed convex free fibres;
changed to the additional explicit ClosedConvexAllowed hypothesis, because
allowed-channel mixing and quantitative optimizer selection are used in the
conversion construction. The unrestricted allowed-subset case is not claimed. -/
theorem fidelity_bounds_ordinary (O : ResourceTheory) (hO : Regular O) (hAllowed : ClosedConvexAllowed O) {p q : Port}
    (E : ChannelChoi p) (N : ChannelChoi q) (hE : E ∈ O.allowed p) (hN : N ∈ O.allowed q)
    (hpure : PureTarget N) :
    gauge O E ((standard O N)⁻¹) ≤ bestFidelity O E N ∧
    bestFidelity O E N ≤ gauge O E ((minimum O N)⁻¹) ∧
    (∃ Theta : ChannelChoi p →ₗ[ℂ] ChannelChoi q, FreeSuperchannel O Theta ∧
      ENNReal.ofReal (worstCaseFidelity (Theta E) N) = bestFidelity O E N) ∧
    (standard O N = ⊤ → gauge O E 0 ≤ bestFidelity O E N) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P32

end
