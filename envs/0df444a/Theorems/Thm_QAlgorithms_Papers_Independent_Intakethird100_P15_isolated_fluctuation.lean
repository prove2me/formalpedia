-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P15_isolated_fluctuation
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P15.isolated_fluctuation
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T05:03:10.774076+00:00
-- url     : https://prove2.me/theorems/06dfc3ab-cabb-43c1-8628-ff516f2bd939
-- title:
--   Isolated-system quantum fluctuation theorem
-- statement:
--   Let $\mathcal H$ be a nonzero complex Hilbert space with a nonempty finite or countable complete orthonormal basis real in a fixed conjugation. The self-adjoint Hamiltonian $H(t)$ is real in that conjugation, periodic with period $t_0>0$, and satisfies $H(-t)=H(t)$. Start at this symmetry origin and observe an integer number of full cycles. Let $U$ be the well-defined unitary strong limit of the chronological infinitesimal slice products, with each slice equal to $\exp(+i\tau H/\hbar)$ and $\hbar>0$.
--
--   Let $\varepsilon_a$ be the eigenvalues of $H(0)$ in the chosen complete real energy eigenbasis, retaining multiplicities. Assume $Z(t)=\sum_a e^{-t\varepsilon_a}<\infty$ for every $t>0$, and fix $\beta>0$. Prepare eigenstate $a$ with probability $e^{-\beta\varepsilon_a}/Z(\beta)$, evolve by $U$, and measure the same $H(0)$. Thus the work $e$ is final minus initial energy. Its atomic law is
--   $$P=\sum_{a,g}\frac{e^{-\beta\varepsilon_a}}{Z(\beta)}|\langle g|U|a\rangle|^2\,\delta_{\varepsilon_g-\varepsilon_a}.$$
--   Here $\delta_x$ is the unit point mass at $x$.
--
--   Writing $r(e)=-e$, the law $P$ is a Borel probability measure and
--   $$r_*P(de)=e^{-\beta e}P(de),\qquad P(\{e\})=e^{\beta e}P(\{-e\})\quad(e\in\mathbb R).$$
--   The two measures $P$ and $r_*P$ are mutually absolutely continuous. The point-mass equation includes zero-probability events and uses no probability ratio.
--
--   This identifies the exact asymmetry between energy gain and energy loss in the cyclic experiment.
-- source:
--   A Quantum Fluctuation Theorem, arXiv:cond-mat/0007360v2, PDF p. 4, Isolated-system quantum fluctuation theorem, abstract and (14)

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

/-- Kurchan, PDF pp.3--4, (8), (14), and abstract p.1: isolated fluctuation theorem.
The same initial Hamiltonian is measured at both ends; all multiplicities are kept.
Point-mass identities hold also at zero mass, without dividing by probabilities. -/
theorem isolated_fluctuation [Countable ι] [Nonempty ι]
    (b : HilbertBasis ι ℂ E) (d : CyclicDrive (Ω := Ω) b)
    (energy : ι → ℝ) (beta : ℝ) (hbeta : 0 < beta)
    (henergy : IsInitialEnergyBasis b d energy) (hheat : HasFiniteHeatTraces energy) :
    let P := workLaw b d.evolution energy beta
    IsProbabilityMeasure P ∧
    reflectedLaw P = P.withDensity (fun e => ENNReal.ofReal (Real.exp (-beta * e))) ∧
    (P ≪ reflectedLaw P) ∧ (reflectedLaw P ≪ P) ∧
    (∀ e : ℝ, (P {e}).toReal = Real.exp (beta * e) * (P {-e}).toReal) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P15
