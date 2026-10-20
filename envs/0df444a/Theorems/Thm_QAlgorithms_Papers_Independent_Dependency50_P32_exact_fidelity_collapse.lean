-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P32_exact_fidelity_collapse
-- name    : QAlgorithms.Papers.Independent.Dependency50.P32.exact_fidelity_collapse
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T14:56:12.293979+00:00
-- url     : https://prove2.me/theorems/e8065363-81a3-467e-a9d2-2210b717daea
-- title:
--   Exact fidelity under reference collapse
-- statement:
--   All Hilbert spaces have strictly positive finite dimension. For each channel type, let $\mathcal O_{\rm all}$ be the closed convex physically allowed family of CPTP maps, with a nonempty closed convex free subset $\mathcal O$; primes indicate the output fibre. Let $\mathbb S$ be the maximal family of deterministic physical superchannels preserving both the allowed structures and the free fibres. Write $F$ for squared Uhlmann fidelity minimized over normalized reference-assisted input states, with an input-sized reference.
--
--   The multiplicative quantities $R_s$, $R_{\max}$, $R_H^\eta$, and $R_{\min}$ are standard robustness, generalized robustness, hypothesis-testing resource, and zero-error ordinary testing resource. Their affine versions use the affine saddle/equal-overlap domains; affine min-resource uses support-projector overlaps and is distinct from zero-error affine testing. Smoothing means the extended infimum over physically allowed channels with fidelity at least $1-\eta$; tolerances at least one give the whole allowed fibre. Unless specified otherwise, smoothing errors lie in $[0,1]$.
--
--   For a reference-assisted purity-preserving target $N$, both collapse implications hold:
--   $$
--   \begin{aligned}
--   R_{\min}(N)=R_s(N)&\Longrightarrow\max_{\Theta\in\mathbb S}F(\Theta(E),N)=G_{\mathcal O}(E;R_{\min}(N)),\\
--   R_{\min,\operatorname{aff}}(N)=R_{\max}(N)&\Longrightarrow\max_{\Theta\in\mathbb S}F(\Theta(E),N)=G_{\operatorname{aff}(\mathcal O)}(E;R_{\max}(N)).
--   \end{aligned}
--   $$
--   Every target monotone uses its output fibre, and both maxima have physical free-superchannel witnesses. In the affine branch, collapse with generalized robustness automatically excludes the undefined zero resource parameter.
--
--   These are the precise tight-fidelity consequences of (D1)-(D2) referred to on p.3.
-- source:
--   One-Shot Manipulation of Dynamical Quantum Resources, arXiv:2012.02215v3, PDF p. 3, Exact fidelity under reference collapse

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P32

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Dependency50.P32

open QAlgorithms.Papers.Independent.Information100.P07 (support)

/-- Tight fidelity sentence on PDF p.3, made precise by (D1)-(D2), pp.12-13:
both reference-collapse branches, each with a maximizing free superchannel.
Source-scope correction: printed p.2 assumes only closed convex free fibres;
changed to the additional explicit ClosedConvexAllowed hypothesis, because
allowed-channel mixing and quantitative optimizer selection are used in the
conversion construction. The unrestricted allowed-subset case is not claimed. -/
theorem exact_fidelity_collapse (O : ResourceTheory) (hO : Regular O) (hAllowed : ClosedConvexAllowed O) {p q : Port}
    (E : ChannelChoi p) (N : ChannelChoi q) (hE : E ∈ O.allowed p) (hN : N ∈ O.allowed q)
    (hpure : PureTarget N) :
    (minimum O N = standard O N →
      bestFidelity O E N = gauge O E ((minimum O N)⁻¹) ∧
      ∃ Theta : ChannelChoi p →ₗ[ℂ] ChannelChoi q, FreeSuperchannel O Theta ∧
        ENNReal.ofReal (worstCaseFidelity (Theta E) N) = bestFidelity O E N) ∧
    (minimumAffine O N = maximal O N →
      bestFidelity O E N = gaugeAffine O E ((maximal O N)⁻¹) ∧
      ∃ Theta : ChannelChoi p →ₗ[ℂ] ChannelChoi q, FreeSuperchannel O Theta ∧
        ENNReal.ofReal (worstCaseFidelity (Theta E) N) = bestFidelity O E N) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P32

end
