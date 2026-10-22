-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P50_gauge_transformations
-- name    : QAlgorithms.Papers.Independent.Claimed50.P50.gauge_transformations
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T12:19:59.707144+00:00
-- url     : https://prove2.me/theorems/a4dd5c0d-a2cd-49bc-bea9-b2a6dbab2b57
-- title:
--   Gauge transformations preserve the standard form and obey (23)
-- statement:
--   Let $H,H_0$ be complex Hilbert spaces and $D\subset H$ a dense complex linear subspace. Let $L:D\to H\otimes H_0$, $K:D\to H$ be linear operators satisfying $\|L\psi\|^2\le2\operatorname{Re}\langle\psi,K\psi\rangle$ on $D$, and let $\ell$ be their standard form (8). For a unitary $D_{\mathrm{noise}}$ on $H_0$, $a\in H_0$, and $b\in\mathbb R$, write $A_a\psi=\psi\otimes a$ and set
--
--   $$L'=(I\otimes D_{\mathrm{noise}})L+A_a,\qquad K'=K+A_a^*(I\otimes D_{\mathrm{noise}})L+(\|a\|^2/2-ib)I.$$
--
--   The transformed operators have the same standard form and satisfy the same dissipativity inequality. These transformations act by the multiplication
--
--   $$(D',a',b')(D,a,b)=(D'D,D'a+a',b+b'-\operatorname{Im}\langle a',D'a\rangle).$$
--
--   This multiplication is associative, has identity $(I,0,0)$ and inverse $(D^*,-D^*a,-b)$, and composition of transformations agrees with it. This is the explicit algebraic gauge symmetry; no conclusion about equivalence of all representations or the unprovided minimality convention is included.
-- source:
--   Covariant Quantum Dynamical Semigroups: Unbounded generators, arXiv:quant-ph/9701037v1, PDF p. 9, §4: standard-representation gauge transformations and group law (23)

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P50

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P50

open scoped TensorProduct BigOperators

variable {H N : Type*}

variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable [NormedAddCommGroup N] [InnerProductSpace ℂ N] [CompleteSpace N]

/-- Holevo, arXiv:quant-ph/9701037v1, PDF p.9, gauge transformations and (23).
They preserve (8) and dissipativity and form a group acting on standard pairs.
This algebraic result does not assume the unspecified minimality convention
used later in Theorem 1. -/
theorem gauge_transformations {D : Submodule ℂ H}
    (hDense : Dense (D : Set H)) (S : StandardData (N := N) D)
    (hDiss : IsDissipative S) :
    (∀ g : NoiseGauge N,
      (∀ (psi : D) (X : H →L[ℂ] H) (phi : D),
        standardForm (gaugeAction g S) psi X phi = standardForm S psi X phi) ∧
      IsDissipative (gaugeAction g S)) ∧
    (∀ gp g : NoiseGauge N,
      gaugeAction gp (gaugeAction g S) = gaugeAction (gaugeMul gp g) S) ∧
    (gaugeAction gaugeIdentity S = S) ∧
    (∀ gpp gp g : NoiseGauge N,
      gaugeMul gpp (gaugeMul gp g) = gaugeMul (gaugeMul gpp gp) g) ∧
    (∀ g : NoiseGauge N,
      gaugeMul gaugeIdentity g = g ∧ gaugeMul g gaugeIdentity = g ∧
      gaugeMul (noiseGaugeInverse g) g = gaugeIdentity ∧
      gaugeMul g (noiseGaugeInverse g) = gaugeIdentity) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P50

end
