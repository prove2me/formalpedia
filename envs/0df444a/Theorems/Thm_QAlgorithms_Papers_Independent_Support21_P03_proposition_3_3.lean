-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P03_proposition_3_3
-- name    : QAlgorithms.Papers.Independent.Support21.P03.proposition_3_3
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T03:31:44.946985+00:00
-- url     : https://prove2.me/theorems/838a3313-fa2e-4458-8b63-b6f7d2427d7b
-- title:
--   Finite-time Evans–Searles theorem
-- statement:
--   Let $(M,\mathcal F,\omega)$ be a probability space and let $\phi^t$ be a group of measurable automorphisms, jointly measurable in time and configuration, with time domain $\mathbb Z$ or $\mathbb R$. Assume that $\omega_t=(\phi^t)_*\omega$ is equivalent to $\omega$ for every time. Set $\ell_t=\log(d\omega_t/d\omega)$ and $c^t=\ell_t\circ\phi^t$. Equalities of observables are modulo $\omega$-null sets. Write $e_t(\alpha)=\log\int e^{\alpha\ell_t}\,d\omega$, retaining extended moment values. A time reversal $\vartheta$ is a measurable involution with $\vartheta\phi^t=\phi^{-t}\vartheta$ and $\vartheta_*\omega=\omega$.
--
--   For $t\ne0$, put $\Sigma^t=c^t/t$, let $P_t$ be its law under $\omega$, and let $\overline P_t$ be the law of $-\Sigma^t$. If the system is time reversal invariant, these laws are equivalent and
--   $$\frac{d\overline P_t}{dP_t}(s)=e^{-ts}\quad(P_t\text{-almost everywhere}).$$
--
--   The measure identity retains the content of the fluctuation relation even on events of probability zero.
-- source:
--   Entropic Fluctuations in Statistical Mechanics I. Classical Dynamical Systems, arXiv:1009.3248v2, PDF p. 10, Proposition 3.3

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P03

noncomputable section

open MeasureTheory Filter Set

open scoped ENNReal Topology BigOperators

namespace QAlgorithms.Papers.Independent.Support21.P03

variable {K : TimeKind} {M : Type*} [MeasurableSpace M]

/-- Proposition 3.3, PDF p.10: finite-time Evans--Searles theorem.
Time zero is excluded because (3.5) has no source convention there. -/
theorem proposition_3_3 (D : NonsingularSystem K M) (theta : M ≃ᵐ M)
    (hTRI : IsTimeReversal D theta) (t : K.Carrier) (ht : timeValue K t ≠ 0) :
    ESIdentity (entropyLaw D t) (timeValue K t) := by sorry

end QAlgorithms.Papers.Independent.Support21.P03

end
