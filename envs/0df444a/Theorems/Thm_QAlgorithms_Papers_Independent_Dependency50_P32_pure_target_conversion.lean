-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P32_pure_target_conversion
-- name    : QAlgorithms.Papers.Independent.Dependency50.P32.pure_target_conversion
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T14:47:07.994206+00:00
-- url     : https://prove2.me/theorems/b6ac0381-63c6-4188-9408-2d4792be59a1
-- title:
--   Theorem 3: pure-target conversion and sharper error
-- statement:
--   All Hilbert spaces have strictly positive finite dimension. For each channel type, let $\mathcal O_{\rm all}$ be the closed convex physically allowed family of CPTP maps, with a nonempty closed convex free subset $\mathcal O$; primes indicate the output fibre. Let $\mathbb S$ be the maximal family of deterministic physical superchannels preserving both the allowed structures and the free fibres. Write $F$ for squared Uhlmann fidelity minimized over normalized reference-assisted input states, with an input-sized reference.
--
--   The multiplicative quantities $R_s$, $R_{\max}$, $R_H^\eta$, and $R_{\min}$ are standard robustness, generalized robustness, hypothesis-testing resource, and zero-error ordinary testing resource. Their affine versions use the affine saddle/equal-overlap domains; affine min-resource uses support-projector overlaps and is distinct from zero-error affine testing. Smoothing means the extended infimum over physically allowed channels with fidelity at least $1-\eta$; tolerances at least one give the whole allowed fibre. Unless specified otherwise, smoothing errors lie in $[0,1]$.
--
--   Suppose $(\operatorname{id}\otimes N)(\psi)$ is pure for every normalized pure input $\psi$ on an input-sized reference and the channel input. A free conversion of $E$ to $N$ with fidelity at least $1-\epsilon$ implies both
--   $$
--   R_{H,\mathcal O}^\epsilon(E)\ge R_{\min,\mathcal O'}(N),\qquad
--   R_{H,\operatorname{aff}(\mathcal O)}^\epsilon(E)\ge R_{\min,\operatorname{aff}(\mathcal O')}(N).
--   $$
--   Conversely, either
--   $$
--   R_{H,\mathcal O}^\epsilon(E)\ge R_{s,\mathcal O'}^\delta(N)
--   \quad\text{or}\quad
--   R_{H,\operatorname{aff}(\mathcal O)}^\epsilon(E)\ge R_{\max,\mathcal O'}^\delta(N)
--   $$
--   ensures an actual free conversion with fidelity at least $1-\epsilon-\delta$.
--
--   Purity sharpens the coefficient of $\delta$ from two to one. No strict bound on $\epsilon+\delta$ is imposed; when this sum is at least one the fidelity lower bound is trivial.
-- source:
--   One-Shot Manipulation of Dynamical Quantum Resources, arXiv:2012.02215v3, PDF p. 3, Theorem 3: pure-target conversion and sharper error

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P32

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Dependency50.P32

open QAlgorithms.Papers.Independent.Information100.P07 (support)

/-- Theorem 3, PDF pp.3,11-12: normalized reference-assisted pure target;
both necessary inequalities and both alternative sufficient tests. There is
no strict restriction on e+d; fidelity bounds with e+d>=1 remain meaningful.
Source-scope correction: printed p.2 assumes only closed convex free fibres;
changed to the additional explicit ClosedConvexAllowed hypothesis, because
allowed-channel mixing and quantitative optimizer selection are used in the
conversion construction. The unrestricted allowed-subset case is not claimed. -/
theorem pure_target_conversion (O : ResourceTheory) (hO : Regular O) (hAllowed : ClosedConvexAllowed O) {p q : Port}
    (E : ChannelChoi p) (N : ChannelChoi q) (hE : E ∈ O.allowed p) (hN : N ∈ O.allowed q)
    (hpure : PureTarget N) (e d : ℝ) (he : 0 ≤ e) (he1 : e ≤ 1)
    (hd : 0 ≤ d) (hd1 : d ≤ 1) :
    (Converts O E N e → minimum O N ≤ testing O E e ∧
      minimumAffine O N ≤ testingAffine O E e) ∧
    ((smooth O (standard O) d N ≤ testing O E e ∨
      smooth O (maximal O) d N ≤ testingAffine O E e) → Converts O E N (e + d)) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P32

end
