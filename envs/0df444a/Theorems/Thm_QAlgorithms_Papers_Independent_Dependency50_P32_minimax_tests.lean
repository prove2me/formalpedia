-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P32_minimax_tests
-- name    : QAlgorithms.Papers.Independent.Dependency50.P32.minimax_tests
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T14:48:38.867403+00:00
-- url     : https://prove2.me/theorems/bac10767-7bc9-460a-bd52-d26c0a87e2ac
-- title:
--   Lemma 5: ordinary and affine minimax tests
-- statement:
--   All Hilbert spaces have strictly positive finite dimension. For each channel type, let $\mathcal O_{\rm all}$ be any physically allowed family of CPTP maps, with a nonempty closed convex free subset $\mathcal O$; primes indicate the output fibre. Let $\mathbb S$ be the maximal family of deterministic physical superchannels preserving both the allowed structures and the free fibres. Write $F$ for squared Uhlmann fidelity minimized over normalized reference-assisted input states, with an input-sized reference.
--
--   The multiplicative quantities $R_s$, $R_{\max}$, $R_H^\eta$, and $R_{\min}$ are standard robustness, generalized robustness, hypothesis-testing resource, and zero-error ordinary testing resource. Their affine versions use the affine saddle/equal-overlap domains; affine min-resource uses support-projector overlaps and is distinct from zero-error affine testing. Smoothing means the extended infimum over physically allowed channels with fidelity at least $1-\eta$; tolerances at least one give the whole allowed fibre. Unless specified otherwise, smoothing errors lie in $[0,1]$.
--
--   For a normalized pure reference-assisted input $\psi$, write $E_\psi=(\operatorname{id}\otimes E)(\psi)$ and $M_\psi=(\operatorname{id}\otimes M)(\psi)$, and use the Hilbert--Schmidt pairing. Joint optimization over $\psi$, the effect $P$, and the real scalar $\lambda$ gives the attained minima
--   $$
--   \begin{aligned}
--   R_{H,\mathcal O}^\epsilon(E)^{-1}
--   &=\min\{\lambda:0\le P\le I,\ \langle P,E_\psi\rangle\ge1-\epsilon,\ \langle P,M_\psi\rangle\le\lambda\ \forall M\in\mathcal O\},\\
--   R_{H,\operatorname{aff}(\mathcal O)}^\epsilon(E)^{-1}
--   &=\min\{\lambda:0\le P\le I,\ \langle P,E_\psi\rangle\ge1-\epsilon,\ \langle P,M_\psi\rangle=\lambda\ \forall M\in\mathcal O\}.
--   \end{aligned}
--   $$
--   The equal-overlap affine constraint is essential. This minimax identity converts the original free-channel-first optimization into a single jointly feasible testing program.
-- source:
--   One-Shot Manipulation of Dynamical Quantum Resources, arXiv:2012.02215v3, PDF p. 8, Lemma 5: ordinary and affine minimax tests

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P32

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Dependency50.P32

open QAlgorithms.Papers.Independent.Information100.P07 (support)

/-- Lemma 5, PDF pp.8-9 (A2)-(A7): ordinary and affine minimax test programs.
IsLeast asserts both the minimum value and an attaining (psi,P,lambda) triple.
The affine constraint is equality for EVERY free channel. -/
theorem minimax_tests (O : ResourceTheory) (hO : Regular O) {p : Port}
    (E : ChannelChoi p) (hE : E ∈ O.allowed p) (e : ℝ) (he : 0 ≤ e) (he1 : e ≤ 1) :
    IsLeast (pureTestValues O E e false) ((testing O E e)⁻¹) ∧
    IsLeast (pureTestValues O E e true) ((testingAffine O E e)⁻¹) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P32

end
