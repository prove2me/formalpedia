-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P01_classicalCocycleAndEntropy
-- name    : QAlgorithms.Papers.Independent.Next46.P01.classicalCocycleAndEntropy
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T18:29:47.028507+00:00
-- url     : https://prove2.me/theorems/1968c84a-82c8-4d41-9aca-83293ca103f6
-- title:
--   Classical entropy cocycle and extended entropy balance
-- statement:
--   Let $X$ be a compact metric space with a jointly continuous real group of homeomorphisms $\phi_t$, and let $\omega$ be a non-invariant Borel probability measure. Write $\omega_t=(\phi_t)_*\omega$, and assume that $\omega_t$ and $\omega$ are mutually absolutely continuous for every $t\in\mathbb R$. Define
--   $$
--   c^t=\log\left(\frac{d\omega_t}{d\omega}\right)\circ\phi_t.
--   $$
--   For every $t,s\in\mathbb R$,
--   $$
--   c^{t+s}=c^t+c^s\circ\phi_t\quad\omega\text{-almost everywhere},\qquad
--   \operatorname{Ent}(\omega_t\mid\omega)=-\int_X c^t\,d\omega.
--   $$
--   Here $\operatorname{Ent}(\nu\mid\mu)=-D(\nu\Vert\mu)\in[-\infty,0]$. The expectation is the extended signed integral: its negative part is finite for this cocycle, while its positive part can be infinite. This gives entropy balance before continuity or differentiability of the cocycle is imposed.
-- source:
--   Entropic Fluctuations in Statistical Mechanics II. Quantum Dynamical Systems, arXiv:2409.15485v2, PDF p. 21, proposition-2.13

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P01

noncomputable section

open Filter MeasureTheory Set

open scoped BigOperators ComplexConjugate ComplexOrder Matrix.Norms.L2Operator Topology ENNReal

namespace QAlgorithms.Papers.Independent.Next46.P01

section Classical

variable (X : Type*) [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]

variable {X}

/-- Proposition 2.13: arXiv:2409.15485v2, PDF p.21. The additive law is a.e.,
and the entropy/expectation identity is extended real, with no (Cl2) or (Cl3). -/
theorem classicalCocycleAndEntropy (D : ClassicalFlowSystem X)
    (hnoninvariant : ClassicalNonInvariant D) :
    (∀ t s : ℝ,
      classicalCocycle D (t + s) =ᵐ[(D.omega : Measure X)]
        fun x => classicalCocycle D t x + classicalCocycle D s (D.flow t x)) ∧
    (∀ t : ℝ,
      classicalRelativeEntropy (classicalEvolved D (D.omega : Measure X) t) (D.omega : Measure X) =
        -extendedExpectation (D.omega : Measure X) (classicalCocycle D t)) := by sorry

end Classical

end QAlgorithms.Papers.Independent.Next46.P01

end
