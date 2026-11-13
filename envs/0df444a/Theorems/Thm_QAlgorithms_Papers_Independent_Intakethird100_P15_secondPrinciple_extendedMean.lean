-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P15_secondPrinciple_extendedMean
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P15.secondPrinciple_extendedMean
-- status  : Proved
-- author  : @Gohan
-- created : 2026-11-01T05:06:38.264242+00:00
-- url     : https://prove2.me/theorems/3d70ab4f-e256-4d16-b0b3-a3e76331a13e
-- title:
--   Second principle with possibly infinite mean work
-- statement:
--   Let $\mathcal H$ be a nonzero complex Hilbert space with a nonempty finite or countable complete orthonormal basis real in a fixed conjugation. The self-adjoint Hamiltonian $H(t)$ is real in that conjugation, periodic with period $t_0>0$, and satisfies $H(-t)=H(t)$. Start at this symmetry origin and observe an integer number of full cycles. Let $U$ be the well-defined unitary strong limit of the chronological infinitesimal slice products, with each slice equal to $\exp(+i\tau H/\hbar)$ and $\hbar>0$.
--
--   Let $\varepsilon_a$ be the eigenvalues of $H(0)$ in the chosen complete real energy eigenbasis, retaining multiplicities. Assume $Z(t)=\sum_a e^{-t\varepsilon_a}<\infty$ for every $t>0$, and fix $\beta>0$. Prepare eigenstate $a$ with probability $e^{-\beta\varepsilon_a}/Z(\beta)$, evolve by $U$, and measure the same $H(0)$. Thus the work $e$ is final minus initial energy. Its atomic law is
--   $$P=\sum_{a,g}\frac{e^{-\beta\varepsilon_a}}{Z(\beta)}|\langle g|U|a\rangle|^2\,\delta_{\varepsilon_g-\varepsilon_a}.$$
--   Here $\delta_x$ is the unit point mass at $x$.
--
--   The negative part $e^-:=\max(-e,0)$ is integrable. Define the signed extended expectation by the positive-part integral minus the negative-part integral; in particular,
--   $$\mathbb E_P e=\int e^+\,dP-\int e^-\,dP\in\mathbb R\cup\{+\infty\}.$$
--   With this convention for the logarithmic expectation as well,
--   $$0=-\frac1\beta\log\mathbb E_P[e^{-\beta e}]\leq-\frac1\beta\mathbb E_P[\log(e^{-\beta e})]=\mathbb E_P e.$$
--   If $e$ is integrable, the extended mean equals the ordinary real integral $\int e\,dP$. No finite-mean assumption is imposed for the main inequality.
--
--   This is the annealed-versus-quenched formulation of the second principle, preserving the placement of each logarithm.
-- source:
--   A Quantum Fluctuation Theorem, arXiv:cond-mat/0007360v2, PDF p. 4, Second principle as annealed/quenched inequality, (16)–(17)

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

/-- Kurchan, PDF p.4, (16)--(17): annealed <= quenched, with the two logarithm
placements preserved. The negative work part is integrable; the extended mean may
be +infinity. The final clause recovers the ordinary expectation if work is integrable.
No finite-mean-work hypothesis is added to the main assertion. -/
theorem secondPrinciple_extendedMean [Countable ι] [Nonempty ι]
    (b : HilbertBasis ι ℂ E) (d : CyclicDrive (Ω := Ω) b)
    (energy : ι → ℝ) (beta : ℝ) (hbeta : 0 < beta)
    (henergy : IsInitialEnergyBasis b d energy) (hheat : HasFiniteHeatTraces energy) :
    let P := workLaw b d.evolution energy beta
    Integrable (fun e : ℝ => max (-e) 0) P ∧
    (∫⁻ e, ENNReal.ofReal (max (-e) 0) ∂P) < ∞ ∧
    (0 : EReal) = ((-(1 / beta) * Real.log (∫ e, Real.exp (-beta * e) ∂P) : ℝ) : EReal) ∧
    ((-(1 / beta) * Real.log (∫ e, Real.exp (-beta * e) ∂P) : ℝ) : EReal) ≤
      ((-(1 / beta) : ℝ) : EReal) * extendedExpectation P (fun e => Real.log (Real.exp (-beta * e))) ∧
    ((-(1 / beta) : ℝ) : EReal) * extendedExpectation P (fun e => Real.log (Real.exp (-beta * e))) =
      extendedExpectation P (fun e => e) ∧
    (Integrable (fun e : ℝ => e) P →
      extendedExpectation P (fun e => e) = (((∫ e : ℝ, e ∂P) : ℝ) : EReal)) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P15
