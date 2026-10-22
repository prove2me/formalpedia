-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P03_es_variational_formula
-- name    : QAlgorithms.Papers.Independent.Support21.P03.es_variational_formula
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T03:41:47.368233+00:00
-- url     : https://prove2.me/theorems/865cb959-6b56-4e6f-abc8-77de1a0b056f
-- title:
--   Normal-state variational formula for the finite ES functional
-- statement:
--   Let $(M,\mathcal F,\omega)$ be a probability space and let $\phi^t$ be a group of measurable automorphisms, jointly measurable in time and configuration, with time domain $\mathbb Z$ or $\mathbb R$. Assume that $\omega_t=(\phi^t)_*\omega$ is equivalent to $\omega$ for every time. Set $\ell_t=\log(d\omega_t/d\omega)$ and $c^t=\ell_t\circ\phi^t$. Equalities of observables are modulo $\omega$-null sets. Write $e_t(\alpha)=\log\int e^{\alpha\ell_t}\,d\omega$, retaining extended moment values. A time reversal $\vartheta$ is a measurable involution with $\vartheta\phi^t=\phi^{-t}\vartheta$ and $\vartheta_*\omega=\omega$.
--
--   Fix $t$ and suppose $\ell_t\in L^\infty(\omega)$. For every real $\alpha$,
--   $$e_t(\alpha)=\sup_{\nu\ll\omega}\{\operatorname{Ent}(\nu\mid\omega)+\alpha\nu(\ell_t)\},\qquad e_t(\alpha)=\log\omega(e^{\alpha\ell_t}),$$
--   where the supremum ranges over countably additive probability measures and $\operatorname{Ent}=-D_{\rm KL}$.
--
--   Essential boundedness makes the linear expectation meaningful for every normal state; infinite relative entropy is retained.
-- source:
--   Entropic Fluctuations in Statistical Mechanics I. Classical Dynamical Systems, arXiv:1009.3248v2, PDF p. 10, es-variational-formula

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P03

noncomputable section

open MeasureTheory Filter Set

open scoped ENNReal Topology BigOperators

namespace QAlgorithms.Papers.Independent.Support21.P03

variable {K : TimeKind} {M : Type*} [MeasurableSpace M]

/-- Equation (3.11), PDF p.10: the supremum ranges over normal probability
measures, and log RN density must be essentially bounded. -/
theorem es_variational_formula (D : NonsingularSystem K M) (t : K.Carrier)
    (hbounded : MemLp (logDensity D t) ∞ (D.omega : Measure M))
    (alpha : ℝ) :
    finiteES D t alpha = sSup {v : EReal | ∃ nu : ProbabilityMeasure M,
      (nu : Measure M) ≪ (D.omega : Measure M) ∧
      v = signedEntropy (nu : Measure M) (D.omega : Measure M) +
        (alpha : EReal) * QAlgorithms.Papers.Independent.Next46.P01.extendedExpectation (nu : Measure M) (logDensity D t)} := by sorry

end QAlgorithms.Papers.Independent.Support21.P03

end
