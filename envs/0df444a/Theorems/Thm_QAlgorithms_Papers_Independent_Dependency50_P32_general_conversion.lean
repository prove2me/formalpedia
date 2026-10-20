-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P32_general_conversion
-- name    : QAlgorithms.Papers.Independent.Dependency50.P32.general_conversion
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T14:45:12.051449+00:00
-- url     : https://prove2.me/theorems/dc54ac78-b4fd-41eb-a3e2-c7823ca50a91
-- title:
--   Theorem 1: general approximate resource conversion
-- statement:
--   All Hilbert spaces have strictly positive finite dimension. For each channel type, let $\mathcal O_{\rm all}$ be the closed convex physically allowed family of CPTP maps, with a nonempty closed convex free subset $\mathcal O$; primes indicate the output fibre. Let $\mathbb S$ be the maximal family of deterministic physical superchannels preserving both the allowed structures and the free fibres. Write $F$ for squared Uhlmann fidelity minimized over normalized reference-assisted input states, with an input-sized reference.
--
--   The multiplicative quantities $R_s$, $R_{\max}$, $R_H^\eta$, and $R_{\min}$ are standard robustness, generalized robustness, hypothesis-testing resource, and zero-error ordinary testing resource. Their affine versions use the affine saddle/equal-overlap domains; affine min-resource uses support-projector overlaps and is distinct from zero-error affine testing. Smoothing means the extended infimum over physically allowed channels with fidelity at least $1-\eta$; tolerances at least one give the whole allowed fibre. Unless specified otherwise, smoothing errors lie in $[0,1]$.
--
--   Let $E\in\mathcal O_{\rm all}$ and $N\in\mathcal O'_{\rm all}$. If some $\Theta\in\mathbb S$ satisfies $F(\Theta(E),N)\ge1-\epsilon$, every extended-real monotone $\mathfrak R$ obeys
--   $$
--   \mathfrak R_{\mathcal O}(E)\ge\mathfrak R_{\mathcal O'}^\epsilon(N),\qquad
--   \mathfrak R_{\mathcal O}^\delta(E)\ge\mathfrak R_{\mathcal O'}^{2(\sqrt\delta+\sqrt\epsilon)}(N)\quad(0\le\delta\le1).
--   $$
--   Conversely, for $\delta\ge0$ with $\epsilon+2\delta<1$, either inequality
--   $$
--   R_{H,\mathcal O}^{\delta}(E)\ge R_{s,\mathcal O'}^\epsilon(N)
--   \quad\text{or}\quad
--   R_{H,\operatorname{aff}(\mathcal O)}^\delta(E)\ge R_{\max,\mathcal O'}^\epsilon(N)
--   $$
--   ensures an actual free $\Theta$ with $F(\Theta(E),N)\ge1-\epsilon-2\delta$. The robustness smoothing infima are attained on the closed allowed target fibre. This attainment is not assumed for an arbitrary monotone.
--
--   These conditions govern general one-shot channel conversion without a purity requirement.
-- source:
--   One-Shot Manipulation of Dynamical Quantum Resources, arXiv:2012.02215v3, PDF p. 2, Theorem 1: general approximate resource conversion

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P32

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Dependency50.P32

open QAlgorithms.Papers.Independent.Information100.P07 (support)

/-- Theorem 1, PDF pp.2,10-11: both necessary monotone inequalities and both
sufficient alternatives. The error 2(sqrt delta+sqrt epsilon) has no outer
square. Arbitrary monotone smoothing is an extended infimum; the printed
minimum is retained separately for the quantitative robustness measures.
Source-scope correction: printed p.2 assumes only closed convex free fibres;
changed to the additional explicit ClosedConvexAllowed hypothesis, because
allowed-channel mixing and quantitative optimizer selection are used in the
conversion construction. The unrestricted allowed-subset case is not claimed. -/
theorem general_conversion (O : ResourceTheory) (hO : Regular O) (hAllowed : ClosedConvexAllowed O) {p q : Port}
    (E : ChannelChoi p) (N : ChannelChoi q) (hE : E ∈ O.allowed p) (hN : N ∈ O.allowed q)
    (e : ℝ) (he : 0 ≤ e) (he1 : e ≤ 1) :
    (Converts O E N e → ∀ (R : ChannelChoi p → EReal) (R' : ChannelChoi q → EReal),
      (∀ Theta : ChannelChoi p →ₗ[ℂ] ChannelChoi q, FreeSuperchannel O Theta →
        ∀ J ∈ O.allowed p, R' (Theta J) ≤ R J) →
      smooth O R' e N ≤ R E ∧
      ∀ d : ℝ, 0 ≤ d → d ≤ 1 →
        smooth O R' (2 * (Real.sqrt d + Real.sqrt e)) N ≤ smooth O R d E) ∧
    (∀ d : ℝ, 0 ≤ d → e + 2 * d < 1 →
      (smooth O (standard O) e N ≤ testing O E d ∨
        smooth O (maximal O) e N ≤ testingAffine O E d) →
      Converts O E N (e + 2 * d)) ∧
    QuantitativeAttainment O N e := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P32

end
