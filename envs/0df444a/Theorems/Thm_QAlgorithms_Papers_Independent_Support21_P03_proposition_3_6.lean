-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P03_proposition_3_6
-- name    : QAlgorithms.Papers.Independent.Support21.P03.proposition_3_6
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T03:33:46.36331+00:00
-- url     : https://prove2.me/theorems/03ef8068-c802-44b5-af16-25d36ce3d436
-- title:
--   Equivalent measure and moment formulations of the finite ES relation
-- statement:
--   Let $(M,\mathcal F,\omega)$ be a probability space and let $\phi^t$ be a group of measurable automorphisms, jointly measurable in time and configuration, with time domain $\mathbb Z$ or $\mathbb R$. Assume that $\omega_t=(\phi^t)_*\omega$ is equivalent to $\omega$ for every time. Set $\ell_t=\log(d\omega_t/d\omega)$ and $c^t=\ell_t\circ\phi^t$. Equalities of observables are modulo $\omega$-null sets. Write $e_t(\alpha)=\log\int e^{\alpha\ell_t}\,d\omega$, retaining extended moment values. A time reversal $\vartheta$ is a measurable involution with $\vartheta\phi^t=\phi^{-t}\vartheta$ and $\vartheta_*\omega=\omega$.
--
--   Fix a nonzero time $t$. Let $P_t$ be the law of $c^t/t$, $\overline P_t$ its reflection, and $e_t(\alpha)=\log\omega(e^{\alpha\ell_t})$. Then
--   $$\left[P_t\sim\overline P_t,\quad\frac{d\overline P_t}{dP_t}(s)=e^{-ts}\right]
--   \quad\Longleftrightarrow\quad
--   \left[\forall\alpha\in\mathbb R,\ e_{-t}(\alpha)=e_{-t}(1-\alpha)\right].$$
--
--   This is an equivalence and imposes no separate time reversal hypothesis.
-- source:
--   Entropic Fluctuations in Statistical Mechanics I. Classical Dynamical Systems, arXiv:1009.3248v2, PDF p. 11, Proposition 3.6

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P03

noncomputable section

open MeasureTheory Filter Set

open scoped ENNReal Topology BigOperators

namespace QAlgorithms.Papers.Independent.Support21.P03

variable {K : TimeKind} {M : Type*} [MeasurableSpace M]

/-- Proposition 3.6, PDF p.11: the symmetry uses e_{-t} on both sides. -/
theorem proposition_3_6 (D : NonsingularSystem K M) (t : K.Carrier)
    (ht : timeValue K t ≠ 0) :
    ESIdentity (entropyLaw D t) (timeValue K t) ↔
      ∀ alpha : ℝ, finiteES D (-t) alpha = finiteES D (-t) (1 - alpha) := by sorry

end QAlgorithms.Papers.Independent.Support21.P03

end
