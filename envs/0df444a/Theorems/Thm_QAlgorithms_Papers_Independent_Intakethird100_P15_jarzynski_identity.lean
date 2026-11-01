-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P15_jarzynski_identity
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P15.jarzynski_identity
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T05:06:04.320289+00:00
-- url     : https://prove2.me/theorems/5b5d9e4a-90e3-48b5-955c-33b70cdda162
-- title:
--   Quantum Jarzynski work identity
-- statement:
--   Let $\mathcal H$ be a nonzero complex Hilbert space with a nonempty finite or countable complete orthonormal basis real in a fixed conjugation. The self-adjoint Hamiltonian $H(t)$ is real in that conjugation, periodic with period $t_0>0$, and satisfies $H(-t)=H(t)$. Start at this symmetry origin and observe an integer number of full cycles. Let $U$ be the well-defined unitary strong limit of the chronological infinitesimal slice products, with each slice equal to $\exp(+i\tau H/\hbar)$ and $\hbar>0$.
--
--   Let $\varepsilon_a$ be the eigenvalues of $H(0)$ in the chosen complete real energy eigenbasis, retaining multiplicities. Assume $Z(t)=\sum_a e^{-t\varepsilon_a}<\infty$ for every $t>0$, and fix $\beta>0$. Prepare eigenstate $a$ with probability $e^{-\beta\varepsilon_a}/Z(\beta)$, evolve by $U$, and measure the same $H(0)$. Thus the work $e$ is final minus initial energy. Its atomic law is
--   $$P=\sum_{a,g}\frac{e^{-\beta\varepsilon_a}}{Z(\beta)}|\langle g|U|a\rangle|^2\,\delta_{\varepsilon_g-\varepsilon_a}.$$
--   Here $\delta_x$ is the unit point mass at $x$.
--
--   The exponential work moment is integrable and satisfies
--   $$\mathbb E_P[e^{-\beta e}]=\int_{\mathbb R}e^{-\beta e}\,P(de)=1.$$
--   The nonnegative Lebesgue integral also equals $1$; the average includes both the canonical initial choice and the final Born outcome.
--
--   This is the cyclic work identity, with zero free-energy difference because the same Hamiltonian is measured twice.
-- source:
--   A Quantum Fluctuation Theorem, arXiv:cond-mat/0007360v2, PDF p. 4, Quantum Jarzynski work identity, (15)

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

/-- Kurchan, PDF p.4, (15): quantum Jarzynski identity, including finiteness of the
nonnegative moment. This averages both Gibbs preparation and the Born outcome;
there is no free-energy difference since the measured Hamiltonian is unchanged. -/
theorem jarzynski_identity [Countable ι] [Nonempty ι]
    (b : HilbertBasis ι ℂ E) (d : CyclicDrive (Ω := Ω) b)
    (energy : ι → ℝ) (beta : ℝ) (hbeta : 0 < beta)
    (henergy : IsInitialEnergyBasis b d energy) (hheat : HasFiniteHeatTraces energy) :
    let P := workLaw b d.evolution energy beta
    Integrable (fun e : ℝ => Real.exp (-beta * e)) P ∧
    (∫ e, Real.exp (-beta * e) ∂P) = 1 ∧
    (∫⁻ e, ENNReal.ofReal (Real.exp (-beta * e)) ∂P) = 1 := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P15
