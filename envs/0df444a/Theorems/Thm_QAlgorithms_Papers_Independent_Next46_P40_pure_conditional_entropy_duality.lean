-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P40_pure_conditional_entropy_duality
-- name    : QAlgorithms.Papers.Independent.Next46.P40.pure_conditional_entropy_duality
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T14:51:35.957147+00:00
-- url     : https://prove2.me/theorems/a3c1675a-12af-458d-8832-f6f32b67f0c5
-- title:
--   Conditional-entropy duality for a pure state
-- statement:
--   Let $A,B,E$ be finite nonzero quantum registers and let $|\psi\rangle^{ABE}$ be a unit vector. All marginals are obtained by partial trace from $|\psi\rangle\langle\psi|$, and $H(X\mid Y)=H(XY)-H(Y)$ denotes conditional von Neumann entropy in bits. Then
--
--   $$H(B\mid E)_\psi=-H(B\mid A)_\psi.$$
--
--   This duality relates the receiver and environment conditional entropies of the same pure state.
-- source:
--   Entanglement-Assisted Capacity of Quantum Multiple-Access Channels, arXiv:quant-ph/0511228v2, PDF p. 4, Lemma 3, (23)

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P40

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Next46.P40

attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P19 (mutualInformation marginalRB associate)

variable {A B C E R S : Type*}

variable [Fintype A] [Fintype B] [Fintype C] [Fintype E] [Fintype R] [Fintype S]

variable [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq E]

variable [DecidableEq R] [DecidableEq S]

/-- PDF p.4, Lemma 3: pure-state conditional-entropy duality.
All density matrices in the formula are computed from the normalized vector. -/
theorem pure_conditional_entropy_duality
    [Nonempty A] [Nonempty B] [Nonempty E]
    (v : EuclideanSpace ℂ ((A × B) × E)) (hv : ‖v‖ = 1) :
    vnEntropy (marginalBC (pureDensity v)) - vnEntropy (traceLeft (pureDensity v)) =
      -(vnEntropy (traceRight (pureDensity v)) -
        vnEntropy (traceRight (traceRight (pureDensity v)))) := by sorry

end QAlgorithms.Papers.Independent.Next46.P40

end
