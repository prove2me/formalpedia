-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P32_dual_cone_programs
-- name    : QAlgorithms.Papers.Independent.Dependency50.P32.dual_cone_programs
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T14:51:25.431506+00:00
-- url     : https://prove2.me/theorems/5fb4ed3c-eaa5-4ca1-b5bc-b5c05d247395
-- title:
--   Equation (A12): cone forms and SDP representability
-- statement:
--   All Hilbert spaces have strictly positive finite dimension. For each channel type, let $\mathcal O_{\rm all}$ be any physically allowed family of CPTP maps, with a nonempty closed convex free subset $\mathcal O$; primes indicate the output fibre. Let $\mathbb S$ be the maximal family of deterministic physical superchannels preserving both the allowed structures and the free fibres. Write $F$ for squared Uhlmann fidelity minimized over normalized reference-assisted input states, with an input-sized reference.
--
--   The multiplicative quantities $R_s$, $R_{\max}$, $R_H^\eta$, and $R_{\min}$ are standard robustness, generalized robustness, hypothesis-testing resource, and zero-error ordinary testing resource. Their affine versions use the affine saddle/equal-overlap domains; affine min-resource uses support-projector overlaps and is distinct from zero-error affine testing. Smoothing means the extended infimum over physically allowed channels with fidelity at least $1-\eta$; tolerances at least one give the whole allowed fibre. Unless specified otherwise, smoothing errors lie in $[0,1]$.
--
--   For Hermitian $X$, set $\mathcal O^*=\{X:\langle X,J_M\rangle\ge0\ \forall M\in\mathcal O\}$ and $\operatorname{aff}(\mathcal O)^*=\{X:\langle X,J_M\rangle=0\ \forall M\in\mathcal O\}$. Put $K=I_{\rm in,out}/d_{\rm in}$. For finite $m\ge1$,
--   $$
--   \begin{aligned}
--   R_{H,\mathcal O}^\epsilon(E)^{-1}&=\min_{\rho,Q,\lambda}\{\lambda:\lambda K-Q\in\mathcal O^*,\ 0\le Q\le\rho\otimes I,\ \langle Q,J_E\rangle\ge1-\epsilon\},\\
--   G_{\mathcal O}(E;m)&=\max_{\rho,W}\{\langle W,J_E\rangle:0\le W\le\rho\otimes I,\ K-mW\in\mathcal O^*\}.
--   \end{aligned}
--   $$
--   The affine formulas replace the positive dual by the annihilator and retain the affine gauge supremum. The test minima and ordinary gauge maximum are attained. If either cone has a finite semidefinite representation, the corresponding full testing and gauge feasible sets have finite semidefinite representations with their displayed linear objectives.
--
--   This is an SDP formulation, not a bit-complexity or numerical-accuracy runtime guarantee.
-- source:
--   One-Shot Manipulation of Dynamical Quantum Resources, arXiv:2012.02215v3, PDF p. 9, Equation (A12): cone forms and SDP representability

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P32

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Dependency50.P32

open QAlgorithms.Papers.Independent.Information100.P07 (support)

/-- Eq.(A12), PDF p.9: concrete dual-cone programs and finite semidefinite
representability implication, for both the positive dual and affine annihilator.
Only SDP representability is claimed; the source gives no numerical runtime bound. -/
theorem dual_cone_programs (O : ResourceTheory) (hO : Regular O) {p : Port}
    (E : ChannelChoi p) (hE : E ∈ O.allowed p) (e m : ℝ)
    (he : 0 ≤ e) (he1 : e ≤ 1) (hm : 1 ≤ m) :
    IsLeast (coneTestValues O E e false) ((testing O E e)⁻¹) ∧
    IsLeast (coneTestValues O E e true) ((testingAffine O E e)⁻¹) ∧
    IsGreatest (coneGaugeValues O E m false) (gauge O E (ENNReal.ofReal (1 / m))) ∧
    gaugeAffine O E (ENNReal.ofReal (1 / m)) = sSup (coneGaugeValues O E m true) ∧
    (∀ aff : Bool, SDPRepresentable (Dual O (p := p) aff) →
      SDPRepresentable (testFeasible O p E e aff) ∧
      SDPRepresentable (gaugeFeasible O p m aff)) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P32

end
