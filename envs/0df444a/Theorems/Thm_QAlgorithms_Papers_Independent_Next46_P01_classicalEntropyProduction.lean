-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P01_classicalEntropyProduction
-- name    : QAlgorithms.Papers.Independent.Next46.P01.classicalEntropyProduction
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T18:31:12.93114+00:00
-- url     : https://prove2.me/theorems/6fda5587-db00-4f27-bc62-d4a6616cccf8
-- title:
--   Classical entropy production and Evans–Searles identities
-- statement:
--   Let $(X,\phi,\omega)$ satisfy the classical assumptions of Proposition 2.13. Assume also that each $c^t$ has a continuous representative and that $t\mapsto c^t\in C(X,\mathbb R)$ is differentiable in the supremum norm at zero. Set $\sigma=\left.\frac{d}{dt}c^t\right|_{t=0}$ and $\sigma_s=\sigma\circ\phi_s$. Then, for every real $t$,
--   $$
--   c^t=\int_0^t\sigma_s\,ds\quad\omega\text{-almost everywhere},\qquad
--   \operatorname{Ent}(\omega_t\mid\omega)=-\int_0^t\omega(\sigma_s)\,ds,\qquad \omega(\sigma)=0.
--   $$
--   The time integrals are oriented when $t<0$. If, in addition, an involutive homeomorphism $\iota$ preserves $\omega$ and satisfies $\iota\phi_t=\phi_{-t}\iota$, then
--   $$
--   c^t\circ\iota=c^{-t},\qquad \sigma\circ\iota=-\sigma\quad\omega\text{-almost everywhere}.
--   $$
--   Let $Q_{\omega,t}=(c^t)_*\omega$ and $F_{\omega,t}(\alpha)=\int_X e^{-\alpha c^t(x)}\,d\omega(x)$ for $\alpha\in\mathbb C$. For every real $t$ and complex $\alpha$,
--   $$
--   F_{\omega,t}(\alpha)=\overline{F_{\omega,t}(1-\overline\alpha)}.
--   $$
--   Finally, $\overline Q_{\omega,t}=(-\operatorname{id})_*Q_{\omega,t}$ and $Q_{\omega,t}$ are mutually absolutely continuous and
--   $$
--   \frac{d\overline Q_{\omega,t}}{dQ_{\omega,t}}(s)=e^{-s}\quad Q_{\omega,t}\text{-almost everywhere}.
--   $$
--   These are the classical entropy-balance and finite-time fluctuation identities. The a.e. formulation makes them independent of how continuous representatives are defined on null open sets.
-- source:
--   Entropic Fluctuations in Statistical Mechanics II. Quantum Dynamical Systems, arXiv:2409.15485v2, PDF p. 22, theorem-2.14

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P01

noncomputable section

open Filter MeasureTheory Set

open scoped BigOperators ComplexConjugate ComplexOrder Matrix.Norms.L2Operator Topology ENNReal

namespace QAlgorithms.Papers.Independent.Next46.P01

section Classical

variable (X : Type*) [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]

variable {X}

/-- Theorem 2.14: arXiv:2409.15485v2, PDF p.22, all five clauses.
Equalities of continuous representatives are stated a.e., avoiding arbitrary
values on null open sets. Integrals from 0 to negative t are oriented.
Only clauses (3)--(5) are conditional on TRI. -/
theorem classicalEntropyProduction (D : RegularClassicalSystem X)
    (hnoninvariant : ClassicalNonInvariant D.toClassicalFlowSystem) :
    (∀ t : ℝ,
      ((fun x => D.continuousCocycle t x) =ᵐ[(D.omega : Measure X)]
        fun x => ∫ s in (0 : ℝ)..t, classicalProduction D (D.flow s x)) ∧
      classicalRelativeEntropy (classicalEvolved D.toClassicalFlowSystem (D.omega : Measure X) t)
        (D.omega : Measure X) =
          ((-(∫ s in (0 : ℝ)..t, ∫ x, classicalProduction D (D.flow s x)
            ∂(D.omega : Measure X)) : ℝ) : EReal)) ∧
    (∫ x, classicalProduction D x ∂(D.omega : Measure X)) = 0 ∧
    (∀ iota : X ≃ₜ X, ClassicalTRI D.toClassicalFlowSystem iota →
      (∀ t : ℝ, (fun x => D.continuousCocycle t (iota x)) =ᵐ[(D.omega : Measure X)]
        fun x => D.continuousCocycle (-t) x) ∧
      ((fun x => classicalProduction D (iota x)) =ᵐ[(D.omega : Measure X)]
        fun x => -classicalProduction D x) ∧
      (∀ (t : ℝ) (alpha : ℂ),
        classicalFunctional D (D.omega : Measure X) t alpha =
          conj (classicalFunctional D (D.omega : Measure X) t (1 - conj alpha))) ∧
      (∀ t : ℝ,
        let Q := classicalLaw D (D.omega : Measure X) t
        let reflected := Measure.map (fun s : ℝ => -s) Q
        reflected ≪ Q ∧ Q ≪ reflected ∧
          (∀ᵐ s ∂Q, reflected.rnDeriv Q s = ENNReal.ofReal (Real.exp (-s))))) := by sorry

end Classical

end QAlgorithms.Papers.Independent.Next46.P01

end
