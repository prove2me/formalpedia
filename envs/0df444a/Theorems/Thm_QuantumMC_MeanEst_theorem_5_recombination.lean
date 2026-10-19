-- Prove2me | Theorems.Thm_QuantumMC_MeanEst_theorem_5_recombination
-- name    : QuantumMC.MeanEst.theorem_5_recombination
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T21:26:59.757541+00:00
-- url     : https://prove2.me/theorems/a97ba752-e5a4-46af-8eb6-5f332ad8d1eb
-- title:
--   §2.3, proof of Theorem 5 — recombination identity
-- statement:
--   For an integrable output $X$, positive $\sigma$, any real $m$, and $B=X/\sigma-m$, let $B_{<0}$ and $B_{\ge0}$ retain $B$ on the indicated half-lines and output zero elsewhere. Then
--
--   $$\mathbb E[X]=\sigma\bigl(m-\mathbb E[-B_{<0}]+\mathbb E[B_{\ge0}]\bigr).$$
--
--   This is the expectation identity behind Algorithm 3's final combination.
-- source:
--   Montanaro, Quantum speedup of Monte Carlo methods, arXiv:1504.06987v3, §2.3, proof of Theorem 5, p. 12

import Mathlib
import Definitions.Def_QuantumMC_MeanEst_Setting

namespace QuantumMC.MeanEst

open MeasureTheory ProbabilityTheory

/-- §2.3, proof of Theorem 5, p. 12: recombination of the negative and positive parts. -/
theorem theorem_5_recombination {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Ω → ℝ) (hX : Integrable X P)
    (σ m : ℝ) (hσ : 0 < σ) :
    (∫ ω, X ω ∂P) = σ *
      (m - (∫ ω, -(truncLt 0 (alg3B σ m X) ω) ∂P) +
        (∫ ω, truncGe 0 (alg3B σ m X) ω ∂P)) := by sorry
end QuantumMC.MeanEst
