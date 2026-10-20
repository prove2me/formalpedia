-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P32_choi_gauges
-- name    : QAlgorithms.Papers.Independent.Dependency50.P32.choi_gauges
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T14:50:47.06989+00:00
-- url     : https://prove2.me/theorems/4a6c9a26-0e62-4b8e-8163-d4200375f422
-- title:
--   Equation (A10): Choi fidelity gauges
-- statement:
--   All Hilbert spaces have strictly positive finite dimension. For each channel type, let $\mathcal O_{\rm all}$ be any physically allowed family of CPTP maps, with a nonempty closed convex free subset $\mathcal O$; primes indicate the output fibre. Let $\mathbb S$ be the maximal family of deterministic physical superchannels preserving both the allowed structures and the free fibres. Write $F$ for squared Uhlmann fidelity minimized over normalized reference-assisted input states, with an input-sized reference.
--
--   The multiplicative quantities $R_s$, $R_{\max}$, $R_H^\eta$, and $R_{\min}$ are standard robustness, generalized robustness, hypothesis-testing resource, and zero-error ordinary testing resource. Their affine versions use the affine saddle/equal-overlap domains; affine min-resource uses support-projector overlaps and is distinct from zero-error affine testing. Smoothing means the extended infimum over physically allowed channels with fidelity at least $1-\eta$; tolerances at least one give the whole allowed fibre. Unless specified otherwise, smoothing errors lie in $[0,1]$.
--
--   Let $J_E$ be the unnormalized Choi matrix and let $m\ge1$ be finite. Define $G_{\mathcal O}(E;m)$ by maximizing $\langle W,E_\psi\rangle$ over normalized pure reference-assisted $\psi$ and effects $W$ with free-channel overlaps at most $1/m$; the affine gauge requires equality for every free channel. Then
--   $$
--   \begin{aligned}
--   G_{\mathcal O}(E;m)&=\max_{\rho,W}\{\langle W,J_E\rangle:0\le W\le\rho\otimes I,\ \langle W,J_M\rangle\le1/m\ \forall M\in\mathcal O\},\\
--   G_{\operatorname{aff}(\mathcal O)}(E;m)&=\sup_{\rho,W}\{\langle W,J_E\rangle:0\le W\le\rho\otimes I,\ \langle W,J_M\rangle=1/m\ \forall M\in\mathcal O\}.
--   \end{aligned}
--   $$
--   Here $\rho$ is a density operator. The ordinary maximum is attained. The same statements hold for reciprocal threshold zero, corresponding to $m=\infty$.
--
--   These identities preserve the distinction between the printed maximum and supremum; they assign no value at $m=0$.
-- source:
--   One-Shot Manipulation of Dynamical Quantum Resources, arXiv:2012.02215v3, PDF p. 9, Equation (A10): Choi fidelity gauges

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P32

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Dependency50.P32

open QAlgorithms.Papers.Independent.Information100.P07 (support)

/-- Eq.(A10), PDF p.9: ordinary attained maximum and affine supremum.
The finite resource parameter m>=1 avoids the undefined printed m=0.
The threshold formulation additionally gives the m=infinity endpoint. -/
theorem choi_gauges (O : ResourceTheory) (hO : Regular O) {p : Port}
    (E : ChannelChoi p) (hE : E ∈ O.allowed p) (m : ℝ) (hm : 1 ≤ m) :
    IsGreatest (choiGaugeValues O E (ENNReal.ofReal (1 / m)) false)
      (gauge O E (ENNReal.ofReal (1 / m))) ∧
    gaugeAffine O E (ENNReal.ofReal (1 / m)) =
      sSup (choiGaugeValues O E (ENNReal.ofReal (1 / m)) true) ∧
    IsGreatest (choiGaugeValues O E 0 false) (gauge O E 0) ∧
    gaugeAffine O E 0 = sSup (choiGaugeValues O E 0 true) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P32

end
