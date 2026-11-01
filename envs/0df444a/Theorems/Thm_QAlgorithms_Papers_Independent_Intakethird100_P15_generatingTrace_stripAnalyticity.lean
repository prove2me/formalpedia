-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P15_generatingTrace_stripAnalyticity
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P15.generatingTrace_stripAnalyticity
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T05:04:38.648788+00:00
-- url     : https://prove2.me/theorems/01d3aa72-e900-470d-b9ca-92b613a7d653
-- title:
--   Holomorphy, boundary continuity, and the printed trace estimate
-- statement:
--   Let $\mathcal H$ be a nonzero complex Hilbert space with a nonempty finite or countable complete orthonormal basis real in a fixed conjugation. The self-adjoint Hamiltonian $H(t)$ is real in that conjugation, periodic with period $t_0>0$, and satisfies $H(-t)=H(t)$. Start at this symmetry origin and observe an integer number of full cycles. Let $U$ be the well-defined unitary strong limit of the chronological infinitesimal slice products, with each slice equal to $\exp(+i\tau H/\hbar)$ and $\hbar>0$.
--
--   Let $\varepsilon_a$ be the eigenvalues of $H(0)$ in the chosen complete real energy eigenbasis, retaining multiplicities. Assume $Z(t)=\sum_a e^{-t\varepsilon_a}<\infty$ for every $t>0$, and fix $\beta>0$. Prepare eigenstate $a$ with probability $e^{-\beta\varepsilon_a}/Z(\beta)$, evolve by $U$, and measure the same $H(0)$. Thus the work $e$ is final minus initial energy. Its atomic law is
--   $$P=\sum_{a,g}\frac{e^{-\beta\varepsilon_a}}{Z(\beta)}|\langle g|U|a\rangle|^2\,\delta_{\varepsilon_g-\varepsilon_a}.$$
--   Here $\delta_x$ is the unit point mass at $x$.
--
--   Define the unnormalized function
--   $$Q(\lambda)=\sum_{a,g}e^{\lambda(\varepsilon_g-\varepsilon_a)}|\langle g|U|a\rangle|^2e^{-\beta\varepsilon_a}.$$
--   It is holomorphic on $-\beta<\operatorname{Re}\lambda<0$, continuous on the closed strip $-\beta\leq\operatorname{Re}\lambda\leq0$, and has absolutely convergent spectral series at every point of that closed strip. In the open strip,
--   $$|Q(\lambda)|^2\leq2Z\bigl(2(\operatorname{Re}\lambda+\beta)\bigr)Z\bigl(-2\operatorname{Re}\lambda\bigr).$$
--   The displayed estimate is not evaluated at the endpoints, where $Z(0)$ can diverge.
--
--   This supplies the convergence and boundary values needed for the source's contour shift.
-- source:
--   A Quantum Fluctuation Theorem, arXiv:cond-mat/0007360v2, PDF p. 4, Strip analyticity and explicit generating-function estimate, (13)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P15

namespace QAlgorithms.Papers.Independent.Intakethird100.P15

open MeasureTheory Filter

open QAlgorithms.Papers.Independent.Information100.P37 (transition)

open QAlgorithms.Papers.Independent.Support21.P03 (reflectedLaw)

open QAlgorithms.Papers.Independent.Next46.P01 (extendedExpectation)

open scoped ENNReal Topology

universe u v w

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

variable {ι : Type v} {Ω : Type w} [MeasurableSpace Ω]

/-- Kurchan, PDF p.4, (13) and its preceding analyticity claim. Q is unnormalized.
The factor 2 is the printed nonsharp constant. Holomorphy is asserted in the open
strip, continuity and finite series values on its closure. The heat-trace bound
is only in the OPEN strip, so no divergent zero-temperature-parameter trace is used.

The general real-observable identity (11) is deferred in this round.
The spectral sums above remain valid definitions for pure-point observables, but
requiring an eigenbasis for D would narrow the source's "any real symmetric
operator". No general trace-symmetry theorem is asserted through that restriction. -/
theorem generatingTrace_stripAnalyticity [Countable ι] [Nonempty ι]
    (b : HilbertBasis ι ℂ E) (d : CyclicDrive (Ω := Ω) b)
    (energy : ι → ℝ) (beta : ℝ) (hbeta : 0 < beta)
    (henergy : IsInitialEnergyBasis b d energy) (hheat : HasFiniteHeatTraces energy) :
    DifferentiableOn ℂ (generatingTrace b d.evolution energy beta)
      {z : ℂ | -beta < z.re ∧ z.re < 0} ∧
    ContinuousOn (generatingTrace b d.evolution energy beta)
      {z : ℂ | -beta ≤ z.re ∧ z.re ≤ 0} ∧
    (∀ z : ℂ, -beta ≤ z.re → z.re ≤ 0 → Summable (qTerm b d.evolution energy beta z)) ∧
    (∀ z : ℂ, -beta < z.re → z.re < 0 →
      ‖generatingTrace b d.evolution energy beta z‖ ^ 2 ≤
        2 * heatTrace energy (2 * (z.re + beta)) * heatTrace energy (-2 * z.re)) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P15
