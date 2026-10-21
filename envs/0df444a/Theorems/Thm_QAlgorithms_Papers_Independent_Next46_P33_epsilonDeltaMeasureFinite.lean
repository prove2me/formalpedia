-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P33_epsilonDeltaMeasureFinite
-- name    : QAlgorithms.Papers.Independent.Next46.P33.epsilonDeltaMeasureFinite
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T14:28:54.265016+00:00
-- url     : https://prove2.me/theorems/e48ab1ea-6fcd-480b-b13a-c04636becc2a
-- title:
--   Uniform absolute continuity on a nonatomic probability space forces finite mass
-- statement:
--   Let $(\Omega,\Sigma,\mu)$ be a nonatomic probability space, meaning that each measurable set of positive measure contains a measurable subset of strictly intermediate measure. Let $\nu$ be any measure on $(\Omega,\Sigma)$. Suppose that for every $\varepsilon>0$ there exists $\delta>0$ such that $\mu(E)<\delta$ implies $\nu(E)<\varepsilon$ for every $E\in\Sigma$. Then
--
--   $$
--   \nu(\Omega)<\infty.
--   $$
--
--   No finiteness or sigma-finiteness of $\nu$ is assumed. This fact connects uniform absolute continuity with finiteness on the diffuse part of a von Neumann algebra.
-- source:
--   Composition Operators on Haagerup $L^p$-spaces, arXiv:math/0603612v2, PDF p. 5, Lemma 3.4

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P33

noncomputable section

open MeasureTheory

open scoped ENNReal

namespace QAlgorithms.Papers.Independent.Next46.P33

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Lemma 3.4, PDF p.5. On a genuinely nonatomic probability space,
epsilon-delta absolute continuity forces finite total mass of nu. No initial
finiteness or sigma-finiteness hypothesis on nu is imposed. -/
theorem epsilonDeltaMeasureFinite
    {Omega : Type*} [MeasurableSpace Omega] (mu nu : Measure Omega)
    [IsProbabilityMeasure mu] (hAtomless : SubsetAtomless mu)
    (hContinuity : MeasureEpsilonDelta nu mu) : nu Set.univ < ⊤ := by sorry

end QAlgorithms.Papers.Independent.Next46.P33

end
