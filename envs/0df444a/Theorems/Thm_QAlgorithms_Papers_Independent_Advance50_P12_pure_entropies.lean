-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P12_pure_entropies
-- name    : QAlgorithms.Papers.Independent.Advance50.P12.pure_entropies
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T10:23:22.165419+00:00
-- url     : https://prove2.me/theorems/79c3adce-d8e3-4ea5-9441-82b16c725801
-- title:
--   §I A: min- and max-entropy of a pure bipartite state
-- statement:
--   All registers are finite-dimensional complex Hilbert spaces of positive dimension, represented in arbitrary orthonormal bases. States are positive semidefinite operators of trace one. All logarithms are binary, and $F(\rho,\sigma)=\|\sqrt\rho\sqrt\sigma\|_1$ denotes root fidelity. Conditional min-entropy optimizes the operator-order definition over every normalized reference state; conditional max-entropy is defined by purification duality.
--
--   Let $|\psi_{AB}\rangle$ be any unit vector, form $\rho_{AB}=|\psi\rangle\langle\psi|$, and compute $\rho_A=\operatorname{tr}_B\rho_{AB}$. Then
--   $$H_{\min}(A|B)_\rho=-\log_2\left(\operatorname{tr}\sqrt{\rho_A}\right)^2,\qquad H_{\max}(A|B)_\rho=\log_2\|\rho_A\|_\infty.$$
--   Here the norm is the operator norm. No full-Schmidt-rank or equal-dimension condition is imposed. These formulas describe the pure-state extreme of conditional min- and max-entropy.
-- source:
--   The operational meaning of min- and max-entropy, arXiv:0807.1338v2, PDF p. 2, Section I A

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P12

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P12

open QAlgorithms

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P07 (CQData cqDensity)

open QAlgorithms.Papers.Independent.Dependency50.P35 (maxRelative elog marginalAB)

open QAlgorithms.Papers.Independent.Information100.P67 (conditionalMinEntropy)

open QAlgorithms.Papers.Independent.Renew46.P35 (traceAdjoint)

open QAlgorithms.Papers.Independent.Support50.P23 (exp2Extended independentProduct)

variable {A B C D X : Type}

variable [Fintype A] [Fintype B] [Fintype C] [Fintype D] [Fintype X]

variable [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D] [DecidableEq X]

/-- PDF p.2, Section I A: both pure-state spectral formulas. The reduced A
state is computed; no equal-dimension or full-Schmidt-rank premise is imposed. -/
theorem pure_entropies [Nonempty A] [Nonempty B]
    (psi : EuclideanSpace ℂ (A × B)) (hpsi : ‖psi‖ = 1) :
    let rho := pureDensity psi
    let rhoA := traceRight rho
    conditionalMinEntropy rho = -elog (((cfc Real.sqrt rhoA).trace.re) ^ 2) ∧
    purificationMaxEntropy rho = elog (specNorm rhoA) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P12

end
