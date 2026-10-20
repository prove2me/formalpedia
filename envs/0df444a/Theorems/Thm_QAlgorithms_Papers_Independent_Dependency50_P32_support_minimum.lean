-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P32_support_minimum
-- name    : QAlgorithms.Papers.Independent.Dependency50.P32.support_minimum
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T14:52:18.079795+00:00
-- url     : https://prove2.me/theorems/be9defd3-6d19-400b-b075-d17b0e2c8fc9
-- title:
--   Equations (A13)-(A14): support-projector min-resource
-- statement:
--   All Hilbert spaces have strictly positive finite dimension. For each channel type, let $\mathcal O_{\rm all}$ be any physically allowed family of CPTP maps, with a nonempty closed convex free subset $\mathcal O$; primes indicate the output fibre. Let $\mathbb S$ be the maximal family of deterministic physical superchannels preserving both the allowed structures and the free fibres. Write $F$ for squared Uhlmann fidelity minimized over normalized reference-assisted input states, with an input-sized reference.
--
--   The multiplicative quantities $R_s$, $R_{\max}$, $R_H^\eta$, and $R_{\min}$ are standard robustness, generalized robustness, hypothesis-testing resource, and zero-error ordinary testing resource. Their affine versions use the affine saddle/equal-overlap domains; affine min-resource uses support-projector overlaps and is distinct from zero-error affine testing. Smoothing means the extended infimum over physically allowed channels with fidelity at least $1-\eta$; tolerances at least one give the whole allowed fibre. Unless specified otherwise, smoothing errors lie in $[0,1]$.
--
--   For $E_\psi=(\operatorname{id}\otimes E)(\psi)$, let $\Pi_{E_\psi}$ be the orthogonal support projector. Then
--   $$
--   R_{\min,\mathcal O}(E)^{-1}=\min_{\psi}\max_{M\in\mathcal O}\langle\Pi_{E_\psi},M_\psi\rangle.
--   $$
--   The outer minimum and each inner maximum are attained. If every $E_\psi$ is pure, this specializes to the attained minimum
--   $$
--   R_{\min,\mathcal O}(E)^{-1}=\min\{\lambda:\langle E_\psi,M_\psi\rangle\le\lambda\ \forall M\in\mathcal O\}.
--   $$
--   Inputs are normalized pure states with an input-sized reference. These formulas identify the ordinary zero-error testing quantity with the support-overlap resource; no affine identification is made.
-- source:
--   One-Shot Manipulation of Dynamical Quantum Resources, arXiv:2012.02215v3, PDF p. 9, Equations (A13)-(A14): support-projector min-resource

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P32

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Dependency50.P32

open QAlgorithms.Papers.Independent.Information100.P07 (support)

/-- (A13)-(A14), PDF pp.9-10: min_psi max_M support formula, including both
attainments, and its pure-output specialization. This is NOT an identification
of affine min-resource with zero-error affine hypothesis testing. -/
theorem support_minimum (O : ResourceTheory) (hO : Regular O) {p : Port}
    (E : ChannelChoi p) (hE : E ∈ O.allowed p) :
    IsLeast (Set.range (supportMaximum O E)) ((minimum O E)⁻¹) ∧
    (∀ v : PureInput p, ∃ M ∈ O.free p,
      supportMaximum O E v =
        ENNReal.ofReal (effectProb (support (pureChannelOutput E v)) (pureChannelOutput M v))) ∧
    (PureTarget E → IsLeast {z | ∃ v : PureInput p, ∃ t : ℝ, 0 ≤ t ∧
      (∀ M ∈ O.free p, effectProb (pureChannelOutput E v) (pureChannelOutput M v) ≤ t) ∧
      z = ENNReal.ofReal t} ((minimum O E)⁻¹)) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P32

end
