-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P33_fullFock_phaseAverage
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P33.fullFock_phaseAverage
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:05:14.188658+00:00
-- url     : https://prove2.me/theorems/dcc26d01-62fd-4ecd-95ea-6712f1c8d5c7
-- title:
--   Uniform coherent-phase average equals the Poisson density
-- statement:
--   Let the single-mode Hilbert space be the full space $\ell^2(\mathbb N;\mathbb C)$, with vacuum occupation $0$. For $z\in\mathbb C$, construct
--
--   $$
--   |z\rangle=e^{-|z|^2/2}\sum_{n=0}^{\infty}\frac{z^n}{\sqrt{n!}}|n\rangle.
--   $$
--
--   Every such constructed vector has these coefficients and norm one, and its projector is a normalized positive trace-class operator. For every $\mu\ge0$, normalized uniform phase integration gives
--
--   $$
--   \int_0^{2\pi}|\sqrt\mu e^{i\theta}\rangle\langle\sqrt\mu e^{i\theta}|\frac{d\theta}{2\pi}
--   =\rho_{\rm Pois}(\mu)
--   =\sum_{n=0}^{\infty}e^{-\mu}\frac{\mu^n}{n!}|n\rangle\langle n|.
--   $$
--
--   Both the integral and series converge in trace norm, and the resulting operator is positive with trace one and the displayed Poisson matrix. The phase law has total mass one. The case $\mu=0$ is vacuum, with the conventional $0^0=1$ term. Rotating the integration variable gives the paper's formulation with any complex $\alpha$ and $\mu=|\alpha|^2$.
--
--   This supplies the full-Fock trace-class interface required by the supporting-paper objective; an entrywise equality or finite photon truncation would be insufficient.
-- source:
--   The Quantum State of a Propagating Laser Field, arXiv:quant-ph/0111157v1, PDF p. 1, Introduction, Eqs.(1)–(2)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P33

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P33

open Filter MeasureTheory

open scoped Topology Matrix ComplexConjugate

attribute [local instance] Classical.propDecidable

open QAlgorithms.Papers.Independent.Dependency50.P39

-- Accepted scalar phase; positive exponential, differing only by commuting scalars.

open QAlgorithms.Papers.Independent.Information100.P75 (phase)

/-- arXiv:quant-ph/0111157v1, PDF p.1, Eqs.(1)–(2). Exact normalized
full-Fock phase average, with both integral and Poisson series in trace norm.
The realization conclusions exclude every accepted constructor's zero fallback. -/
theorem fullFock_phaseAverage (mu : ℝ) (hmu : 0 ≤ mu) :
    IsProbabilityMeasure phaseLaw ∧
    (∀ z : ℂ, (∀ n, coherentKet z n = coherentCoefficient z n) ∧
      ‖coherentKet z‖ = 1 ∧ IsDensity (coherentProjector z)) ∧
    PoissonRealized mu ∧
    TraceIntegral phaseLaw
      (fun theta => coherentProjector ((Real.sqrt mu : ℂ) * phase theta))
      (poissonDensity mu) ∧
    TraceHasSum (fun n : ℕ =>
      ((Real.exp (-mu) * mu ^ n / (Nat.factorial n : ℝ) : ℝ) : ℂ) • fockDyad n n)
      (poissonDensity mu) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P33

end
