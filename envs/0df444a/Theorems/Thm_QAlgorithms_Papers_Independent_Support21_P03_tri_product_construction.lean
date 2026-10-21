-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P03_tri_product_construction
-- name    : QAlgorithms.Papers.Independent.Support21.P03.tri_product_construction
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T03:40:31.824152+00:00
-- url     : https://prove2.me/theorems/9d728c6a-0a48-4754-a9f9-f4a8f4147827
-- title:
--   Time reversal by doubling a dynamical system
-- statement:
--   Let $(M,\mathcal F,\omega)$ be a probability space and let $\phi^t$ be a group of measurable automorphisms, jointly measurable in time and configuration, with time domain $\mathbb Z$ or $\mathbb R$. Assume that $\omega_t=(\phi^t)_*\omega$ is equivalent to $\omega$ for every time. Set $\ell_t=\log(d\omega_t/d\omega)$ and $c^t=\ell_t\circ\phi^t$. Equalities of observables are modulo $\omega$-null sets. Write $e_t(\alpha)=\log\int e^{\alpha\ell_t}\,d\omega$, retaining extended moment values. A time reversal $\vartheta$ is a measurable involution with $\vartheta\phi^t=\phi^{-t}\vartheta$ and $\vartheta_*\omega=\omega$.
--
--   On $M\times M$ take the product probability $\widetilde\omega=\omega\otimes\omega$ and the flow
--   $$\widetilde\phi^t(x,y)=(\phi^t(x),\phi^{-t}(y)).$$
--   This is a nonsingular dynamical system with time reversal $\widetilde\vartheta(x,y)=(y,x)$ preserving $\widetilde\omega$.
--
--   The construction provides a time reversal invariant system from the given system. The introductory phrase about a system which is not TRI explains its use and is not needed for the construction.
-- source:
--   Entropic Fluctuations in Statistical Mechanics I. Classical Dynamical Systems, arXiv:1009.3248v2, PDF p. 8, tri-product-construction

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P03

noncomputable section

open MeasureTheory Filter Set

open scoped ENNReal Topology BigOperators

namespace QAlgorithms.Papers.Independent.Support21.P03

variable {K : TimeKind} {M : Type*} [MeasurableSpace M]

/-- The explicit product construction at the end of §2.5, PDF p.8.
Both the backward second factor and the actual product probability are fixed. -/
theorem tri_product_construction (D : NonsingularSystem K M) :
    ∃ P : NonsingularSystem K (M × M),
      (∀ t z, P.flow t z = (D.flow t z.1, D.flow (-t) z.2)) ∧
      (P.omega : Measure (M × M)) = (D.omega : Measure M).prod (D.omega : Measure M) ∧
      IsTimeReversal P (MeasurableEquiv.prodComm : (M × M) ≃ᵐ (M × M)) := by sorry

end QAlgorithms.Papers.Independent.Support21.P03

end
