-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P24_normal_spectral_representation
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P24.normal_spectral_representation
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T22:56:32.747488+00:00
-- url     : https://prove2.me/theorems/ddfadc81-80a2-4f3d-9de3-80eef3a7f327
-- title:
--   Spectral representation of a closed normal operator
-- statement:
--   Let $H$ be an arbitrary complex Hilbert space, and let $T$ be a closed densely defined normal operator on $H$. There exists a normalized orthogonal projection-valued Borel measure $E$ on $\mathbb C$, acting on $H$ and countably additive in the strong operator topology, such that
--
--   $$
--   T=\int_{\mathbb C} z\,E(dz).
--   $$
--
--   This is equality of operators with their full natural domains. In particular, if $\mu_x(S)=\langle x,E(S)x\rangle$ for Borel sets $S$, the integral has domain
--
--   $$
--   \left\{x\in H:\int_{\mathbb C}|z|^2\,d\mu_x(z)<\infty\right\}.
--   $$
--
--   The measure is projection-valued; no finite-dimensional or separable-Hilbert-space restriction is imposed. This representation extends the bounded spectral theorem to unbounded normal operators.
--
--   **Source correction.** The closedness assumption repairs the omission in printed Definition 2.1. The theorem asserts existence of a spectral measure, without an additional uniqueness or diagonalization conclusion.
--
--   **Formalization Note.** The local PVM-to-operator integral evaluates the unique accepted full measurable functional calculus agreeing with $E$ on all Borel indicators. It returns an actual operator graph, preserving the natural domain.
-- source:
--   Decomposition of Normal Operators and Its Application to Spectral Theorem, arXiv:2006.04644v2, PDF p. 1, Theorem B

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P24

noncomputable section

attribute [local instance] Classical.propDecidable

open Set MeasureTheory

open scoped Topology

open QAlgorithms.Papers.Independent.Claimed50.P05

namespace QAlgorithms.Papers.Independent.Intakenext100.P24

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- Theorem B, PDF p.1, proved on PDF p.4: a normalized Borel PVM represents
T by the integral of z over C, including equality of natural domains.
Source correction requiring independent moderation:
Printed: normality in Definition 2.1 omits closedness.
Changed: assume a closed densely defined normal operator, using accepted Normal.
Why: the proof uses Theorem 1.1 with its closedness requirement, and every
spectral integral is closed, whereas identity on c00 in l2 satisfies the
printed normality equation without being closed. -/
theorem normal_spectral_representation (T : Relation H) (hT : Normal (k := ℂ) T) :
    ∃ E : {A : Set ℂ // MeasurableSet A} → Relation H,
      PVM (k := ℂ) E ∧ T = pvmOperatorIntegral E (scalarIdentity (k := ℂ)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P24

end
