-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P33_coherentMixture_unique
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P33.coherentMixture_unique
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:07:17.306335+00:00
-- url     : https://prove2.me/theorems/279d4801-a1f0-4c55-be73-6d9ceb9be641
-- title:
--   The entire beam family uniquely determines its coherent mixing measure
-- statement:
--   Fix a packet amplitude $a\ge0$ and the family $\rho_N(a)$ of uniform common-phase coherent densities. Let $\nu$ be a probability measure on bounded single-mode operators, concentrated almost surely on normal positive trace-class operators of trace one. Suppose the same measure represents every finite tensor power through genuine trace-class integrals:
--
--   $$
--   \forall N\in\mathbb N,\qquad\int\sigma^{\otimes N}\,d\nu(\sigma)=\rho_N(a).
--   $$
--
--   Then
--
--   $$
--   \nu=(\theta\mapsto|ae^{i\theta}\rangle\langle ae^{i\theta}|)_*\left(\frac{d\theta}{2\pi}\right).
--   $$
--
--   The constructed tensor powers of every single-mode density have their product occupation matrices and are normalized positive trace-class densities. Equality is of measures on operators with their Borel sigma algebra, not on kets with arbitrary global phase.
--
--   This establishes uniqueness for the entire compatible exchangeable beam family. A single finite-$N$ representation is not claimed unique. At $a=0$ the measure is the vacuum point mass.
-- source:
--   The Quantum State of a Propagating Laser Field, arXiv:quant-ph/0111157v1, PDF p. 5, IID, Eqs.(20)–(21)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P33

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P33

open Filter MeasureTheory

open scoped Topology Matrix ComplexConjugate

attribute [local instance] Classical.propDecidable

open QAlgorithms.Papers.Independent.Dependency50.P39

-- Accepted scalar phase; positive exponential, differing only by commuting scalars.

open QAlgorithms.Papers.Independent.Information100.P75 (phase)

/-- arXiv:quant-ph/0111157v1, PDF pp.4–5, Eqs.(20)–(21).
The SAME probability measure represents every tensor power, before N is
quantified. Equality is of measures on density operators, so arbitrary global
phases of kets cannot violate uniqueness. At a=0 the measure is vacuum Dirac. -/
theorem coherentMixture_unique (a : ℝ) (ha : 0 ≤ a)
    (nu : Measure FockOperator) (hnu : IsProbabilityMeasure nu)
    (hdensity : ∀ᵐ X ∂nu, IsDensity X)
    (hrep : ∀ N : ℕ, TraceIntegral nu (fun X => fullFockTensorPower X N) (commonPhase a N)) :
    nu = Measure.map (fun theta => coherentProjector ((a : ℂ) * phase theta)) phaseLaw ∧
    (∀ N (X : FockOperator), IsDensity X →
      HasPacketMatrix (fullFockTensorPower X N) (fun m n => ∏ i, X (fockKet (n i)) (m i)) ∧
      IsPacketDensity (fullFockTensorPower X N)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P33

end
