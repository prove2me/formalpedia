-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P15_bath_fluctuation
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P15.bath_fluctuation
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T05:07:04.840361+00:00
-- url     : https://prove2.me/theorems/45872cd1-4660-4090-b79d-dc57448ac9d8
-- title:
--   Thermostated finite-time fluctuation relation for bath energy plus system observable
-- statement:
--   Let $\mathcal H$ be a nonzero complex Hilbert space with a nonempty finite or countable complete orthonormal basis real in a fixed conjugation. The self-adjoint Hamiltonian $H(t)$ is real in that conjugation, periodic with period $t_0>0$, and satisfies $H(-t)=H(t)$. Start at this symmetry origin and observe an integer number of full cycles. Let $U$ be the well-defined unitary strong limit of the chronological infinitesimal slice products, with each slice equal to $\exp(+i\tau H/\hbar)$ and $\hbar>0$.
--
--   Use a complete real product eigenbasis $|a\rangle_B\otimes|s\rangle_S$, with nonempty finite or countable labels on each tensor factor. Let bath energies be $\epsilon_a^B$ and system observable eigenvalues $o_s$, with $O$ bounded below. Fix $\beta>0$, positive finite normalizers $Z_B=\sum_a e^{-\beta\epsilon_a^B}$ and $Z_O=\sum_s e^{-\beta o_s}$, and require for every $0<\mu<1$ that
--   $$\sum_a e^{-2\beta\mu\epsilon_a^B}<\infty,\qquad\sum_s p_s^{2\mu}<\infty,\quad p_s=\frac{e^{-\beta o_s}}{Z_O}.$$
--   Prepare the uncorrelated product weights $e^{-\beta\epsilon_a^B}p_s/Z_B$. The drive acts on the joint Hilbert space and may include interactions. Measure $D=H_B\otimes I+I\otimes O$ at both ends, so its eigenvalue at $(a,s)$ is $d_{a,s}=\epsilon_a^B+o_s$. Let $P_D$ be the Born law with these initial weights and work $d_{g,r}-d_{a,s}$. Then, for $r(e)=-e$,
--   $$r_*P_D(de)=e^{-\beta e}P_D(de),\qquad P_D(\{e\})=e^{\beta e}P_D(\{-e\}).$$
--   The law is a probability measure and is equivalent to its reflection. The exact measured change includes both bath energy and system $O$, and need not equal the change of the interacting Hamiltonian or bath heat alone.
--
--   This is the finite-time thermostated result; no normalized infinite-bath Gibbs state or large-time limit is asserted.
-- source:
--   A Quantum Fluctuation Theorem, arXiv:cond-mat/0007360v2, PDF p. 6, Thermostated finite-time fluctuation relation for D=H_bath+O, (23)–(26)

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

/-- Kurchan, PDF pp.5--6, (22)--(26): finite-time thermostated fluctuation relation.
The basis indexed by B x S is the tensor-product eigenbasis, so the bath and system
observables commute and D has their sum spectrum. The total driven Hamiltonian may
interact and is not assumed equal to D. A finite bath may have infinite-dimensional
Hilbert space. Every 0 < mu < 1 is included in (26); no large-bath/time limit is taken. -/
theorem bath_fluctuation {B S : Type*} [Countable B] [Nonempty B]
    [Countable S] [Nonempty S]
    (b : HilbertBasis (B × S) ℂ E) (d : CyclicDrive (Ω := Ω) b)
    (bathEnergy : B → ℝ) (systemO : S → ℝ) (beta : ℝ) (hbeta : 0 < beta)
    (hO_lower : ∃ L : ℝ, ∀ s, L ≤ systemO s)
    (hZbath : 0 < heatTrace bathEnergy beta)
    (hZsystem : 0 < heatTrace systemO beta)
    (hbath_beta : Summable (fun a => Real.exp (-beta * bathEnergy a)))
    (hsystem_beta : Summable (fun a => Real.exp (-beta * systemO a)))
    (hbath_strip : ∀ mu : ℝ, 0 < mu → mu < 1 →
      Summable (fun a => Real.exp (-(2 * beta * mu) * bathEnergy a)))
    (hpower : ∀ mu : ℝ, 0 < mu → mu < 1 →
      Summable (fun a => (spectralGibbsWeight systemO beta a) ^ (2 * mu))) :
    let P := preparedWorkLaw b d.evolution (bathObservedEnergy bathEnergy systemO)
      (bathPreparation bathEnergy systemO beta)
    IsProbabilityMeasure P ∧
    reflectedLaw P = P.withDensity (fun e => ENNReal.ofReal (Real.exp (-beta * e))) ∧
    (P ≪ reflectedLaw P) ∧ (reflectedLaw P ≪ P) ∧
    (∀ e : ℝ, (P {e}).toReal = Real.exp (beta * e) * (P {-e}).toReal) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P15
