-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P32_affine_min_gap
-- name    : QAlgorithms.Papers.Independent.Dependency50.P32.affine_min_gap
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T14:52:53.858703+00:00
-- url     : https://prove2.me/theorems/be270174-f27c-4813-95b1-501c0d78fbfc
-- title:
--   Remark: affine testing and affine min-resource can differ
-- statement:
--   All Hilbert spaces have strictly positive finite dimension. For each channel type, let $\mathcal O_{\rm all}$ be the closed convex physically allowed family of CPTP maps, with a nonempty closed convex free subset $\mathcal O$; primes indicate the output fibre. Let $\mathbb S$ be the maximal family of deterministic physical superchannels preserving both the allowed structures and the free fibres. Write $F$ for squared Uhlmann fidelity minimized over normalized reference-assisted input states, with an input-sized reference.
--
--   The multiplicative quantities $R_s$, $R_{\max}$, $R_H^\eta$, and $R_{\min}$ are standard robustness, generalized robustness, hypothesis-testing resource, and zero-error ordinary testing resource. Their affine versions use the affine saddle/equal-overlap domains; affine min-resource uses support-projector overlaps and is distinct from zero-error affine testing. Smoothing means the extended infimum over physically allowed channels with fidelity at least $1-\eta$; tolerances at least one give the whole allowed fibre. Unless specified otherwise, smoothing errors lie in $[0,1]$.
--
--   For $0\le\delta\le1$,
--   $$R_{H,\operatorname{aff}(\mathcal O)}^\delta(E)\ge1.$$
--   If there is no normalized pure input $\psi$ for which $\langle\Pi_{E_\psi},M_\psi\rangle$ is constant over all $M\in\mathcal O$, then
--   $$R_{\min,\operatorname{aff}(\mathcal O)}(E)=0.$$
--   For $0\le\epsilon<1$, either $R_{H,\operatorname{aff}(\mathcal O)}^0(E)\ge R_{\max,\mathcal O'}^\epsilon(N)$ or $R_{\min,\operatorname{aff}(\mathcal O)}(E)\ge R_{\max,\mathcal O'}^\epsilon(N)$ suffices for a free conversion of fidelity at least $1-\epsilon$.
--
--   The empty equal-support-overlap domain is assigned infinite inverse value before inversion. This explains why affine min-resource and zero-error affine testing must remain different interfaces.
-- source:
--   One-Shot Manipulation of Dynamical Quantum Resources, arXiv:2012.02215v3, PDF p. 11, Remark: affine testing and affine min-resource can differ

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P32

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Dependency50.P32

open QAlgorithms.Papers.Independent.Information100.P07 (support)

/-- Remark after Theorem 1, PDF p.11: affine testing is >=1, but affine min
can vanish when the equal-support-overlap domain is empty. Includes both
zero-input-error achievability alternatives explicitly mentioned in the Remark.
Source-scope correction: printed p.2 assumes only closed convex free fibres;
changed to the additional explicit ClosedConvexAllowed hypothesis, because
allowed-channel mixing and quantitative optimizer selection are used in the
conversion construction. The unrestricted allowed-subset case is not claimed. -/
theorem affine_min_gap (O : ResourceTheory) (hO : Regular O) (hAllowed : ClosedConvexAllowed O) {p q : Port}
    (E : ChannelChoi p) (N : ChannelChoi q) (hE : E ∈ O.allowed p) (hN : N ∈ O.allowed q)
    (e d : ℝ) (he : 0 ≤ e) (he1 : e < 1) (hd : 0 ≤ d) (hd1 : d ≤ 1) :
    1 ≤ testingAffine O E d ∧
    ((¬ ∃ v : PureInput p, ∃ t : ℝ,
      ∀ M ∈ O.free p, effectProb (support (pureChannelOutput E v)) (pureChannelOutput M v) = t) →
      minimumAffine O E = 0) ∧
    ((smooth O (maximal O) e N ≤ testingAffine O E 0 ∨
      smooth O (maximal O) e N ≤ minimumAffine O E) → Converts O E N e) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P32

end
