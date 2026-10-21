-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P03_proposition_3_5
-- name    : QAlgorithms.Papers.Independent.Support21.P03.proposition_3_5
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T03:33:12.117979+00:00
-- url     : https://prove2.me/theorems/3f9c4431-329c-4641-8133-04a989853d6d
-- title:
--   Finite entropy-functional symmetries
-- statement:
--   Let $(M,\mathcal F,\omega)$ be a probability space and let $\phi^t$ be a group of measurable automorphisms, jointly measurable in time and configuration, with time domain $\mathbb Z$ or $\mathbb R$. Assume that $\omega_t=(\phi^t)_*\omega$ is equivalent to $\omega$ for every time. Set $\ell_t=\log(d\omega_t/d\omega)$ and $c^t=\ell_t\circ\phi^t$. Equalities of observables are modulo $\omega$-null sets. Write $e_t(\alpha)=\log\int e^{\alpha\ell_t}\,d\omega$, retaining extended moment values. A time reversal $\vartheta$ is a measurable involution with $\vartheta\phi^t=\phi^{-t}\vartheta$ and $\vartheta_*\omega=\omega$.
--
--   For every time $t$ and real $\alpha$,
--   $$e_t(\alpha)=e_{-t}(1-\alpha),\qquad e_t(\alpha)=\log\omega(e^{\alpha\ell_t}).$$
--   If the system is time reversal invariant, also $e_{-t}(\alpha)=e_t(\alpha)$, hence $e_t(\alpha)=e_t(1-\alpha)$.
--
--   The first assertion does not require time reversal.
-- source:
--   Entropic Fluctuations in Statistical Mechanics I. Classical Dynamical Systems, arXiv:1009.3248v2, PDF p. 11, Proposition 3.5

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P03

noncomputable section

open MeasureTheory Filter Set

open scoped ENNReal Topology BigOperators

namespace QAlgorithms.Papers.Independent.Support21.P03

variable {K : TimeKind} {M : Type*} [MeasurableSpace M]

/-- Proposition 3.5, PDF p.11. TRI is local to part (2). -/
theorem proposition_3_5 (D : NonsingularSystem K M) :
    (∀ t alpha, finiteES D t alpha = finiteES D (-t) (1 - alpha)) ∧
    (∀ theta : M ≃ᵐ M, IsTimeReversal D theta →
      ∀ t alpha, finiteES D (-t) alpha = finiteES D t alpha ∧
        finiteES D t alpha = finiteES D t (1 - alpha)) := by sorry

end QAlgorithms.Papers.Independent.Support21.P03

end
