-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P03_proposition_3_2
-- name    : QAlgorithms.Papers.Independent.Support21.P03.proposition_3_2
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T03:31:02.884397+00:00
-- url     : https://prove2.me/theorems/88b60215-1771-47b3-a2e9-c55b2b4532b4
-- title:
--   Entropy cocycle under time reversal
-- statement:
--   Let $(M,\mathcal F,\omega)$ be a probability space and let $\phi^t$ be a group of measurable automorphisms, jointly measurable in time and configuration, with time domain $\mathbb Z$ or $\mathbb R$. Assume that $\omega_t=(\phi^t)_*\omega$ is equivalent to $\omega$ for every time. Set $\ell_t=\log(d\omega_t/d\omega)$ and $c^t=\ell_t\circ\phi^t$. Equalities of observables are modulo $\omega$-null sets. Write $e_t(\alpha)=\log\int e^{\alpha\ell_t}\,d\omega$, retaining extended moment values. A time reversal $\vartheta$ is a measurable involution with $\vartheta\phi^t=\phi^{-t}\vartheta$ and $\vartheta_*\omega=\omega$.
--
--   If a time reversal exists, then for every time $t$,
--   $$c^t\circ\vartheta=c^{-t}\quad\text{almost everywhere}.$$
--
--   This identifies the reversed entropy cocycle.
-- source:
--   Entropic Fluctuations in Statistical Mechanics I. Classical Dynamical Systems, arXiv:1009.3248v2, PDF p. 9, Proposition 3.2

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P03

noncomputable section

open MeasureTheory Filter Set

open scoped ENNReal Topology BigOperators

namespace QAlgorithms.Papers.Independent.Support21.P03

variable {K : TimeKind} {M : Type*} [MeasurableSpace M]

/-- Proposition 3.2, PDF p.9, equation (3.4). -/
theorem proposition_3_2 (D : NonsingularSystem K M) (theta : M ≃ᵐ M)
    (hTRI : IsTimeReversal D theta) :
    ∀ t, ∀ᵐ x ∂(D.omega : Measure M),
      entropyCocycle D t (theta x) = entropyCocycle D (-t) x := by sorry

end QAlgorithms.Papers.Independent.Support21.P03

end
