-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P03_proposition_3_1
-- name    : QAlgorithms.Papers.Independent.Support21.P03.proposition_3_1
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T03:29:59.527791+00:00
-- url     : https://prove2.me/theorems/b8013eb0-72d1-4573-8f51-6e12ec1a547a
-- title:
--   Entropy cocycle identity
-- statement:
--   Let $(M,\mathcal F,\omega)$ be a probability space and let $\phi^t$ be a group of measurable automorphisms, jointly measurable in time and configuration, with time domain $\mathbb Z$ or $\mathbb R$. Assume that $\omega_t=(\phi^t)_*\omega$ is equivalent to $\omega$ for every time. Set $\ell_t=\log(d\omega_t/d\omega)$ and $c^t=\ell_t\circ\phi^t$. Equalities of observables are modulo $\omega$-null sets. Write $e_t(\alpha)=\log\int e^{\alpha\ell_t}\,d\omega$, retaining extended moment values. A time reversal $\vartheta$ is a measurable involution with $\vartheta\phi^t=\phi^{-t}\vartheta$ and $\vartheta_*\omega=\omega$.
--
--   For all times $t,s$,
--   $$c^{t+s}=c^s+c^t\circ\phi^s,\qquad c^0=0,\qquad c^{-t}=-c^t\circ\phi^{-t}.$$
--
--   These identities describe the additive entropy cocycle without assuming a stationary reference state.
-- source:
--   Entropic Fluctuations in Statistical Mechanics I. Classical Dynamical Systems, arXiv:1009.3248v2, PDF p. 8, Proposition 3.1

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P03

noncomputable section

open MeasureTheory Filter Set

open scoped ENNReal Topology BigOperators

namespace QAlgorithms.Papers.Independent.Support21.P03

variable {K : TimeKind} {M : Type*} [MeasurableSpace M]

/-- Proposition 3.1, PDF p.8: all times, including zero and negative time.
Function identities are equality of quotient observables (a.e.). -/
theorem proposition_3_1 (D : NonsingularSystem K M) :
    (∀ t s, ∀ᵐ x ∂(D.omega : Measure M),
      entropyCocycle D (t + s) x = entropyCocycle D s x + entropyCocycle D t (D.flow s x)) ∧
    (∀ᵐ x ∂(D.omega : Measure M), entropyCocycle D 0 x = 0) ∧
    (∀ t, ∀ᵐ x ∂(D.omega : Measure M),
      entropyCocycle D (-t) x = -entropyCocycle D t (D.flow (-t) x)) := by sorry

end QAlgorithms.Papers.Independent.Support21.P03

end
