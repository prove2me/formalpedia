-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P12_minEntropy_guessing
-- name    : QAlgorithms.Papers.Independent.Advance50.P12.minEntropy_guessing
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T10:12:14.595982+00:00
-- url     : https://prove2.me/theorems/e8b7e039-6b23-4d25-97eb-4f277b51561f
-- title:
--   Theorem 1: classical min-entropy is guessing entropy
-- statement:
--   All registers are finite-dimensional complex Hilbert spaces of positive dimension, represented in arbitrary orthonormal bases. States are positive semidefinite operators of trace one. All logarithms are binary, and $F(\rho,\sigma)=\|\sqrt\rho\sqrt\sigma\|_1$ denotes root fidelity. Conditional min-entropy optimizes the operator-order definition over every normalized reference state; conditional max-entropy is defined by purification duality.
--
--   Let $X$ be a nonempty finite alphabet and let $\{p_x,\rho_B^x\}_x$ be an ensemble with $p_x\ge0$, $\sum_xp_x=1$, and each $\rho_B^x$ a density operator, even when $p_x=0$. Form $\rho_{XB}=\sum_xp_x|x\rangle\langle x|\otimes\rho_B^x$. Then
--   $$H_{\min}(X|B)_\rho=-\log_2 p_{\mathrm{guess}}(X|B)_\rho,\qquad p_{\mathrm{guess}}(X|B)_\rho=\max_{\{E_x\}}\sum_xp_x\operatorname{tr}(E_x\rho_B^x).$$
--   The maximum is attained over a single $X$-outcome POVM: $E_x\ge0$ and $\sum_xE_x=I_B$. The success criterion is the ensemble average. This identifies min-entropy with optimal decoding probability.
-- source:
--   The operational meaning of min- and max-entropy, arXiv:0807.1338v2, PDF p. 8, Theorem 1 (continued p.9)

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

/-- PDF pp.8–9, Theorem 1: one POVM optimizes ensemble-average guessing
probability, allowing zero-probability labels and mixed conditional states. -/
theorem minEntropy_guessing [Nonempty X] [Nonempty B]
    (e : CQData X B) (he : e.Valid) :
    conditionalMinEntropy (cqDensity e) = -elog (mixedOptSuccess e.prob e.state) ∧
    ∃ m : X → Matrix B B ℂ, IsPOVM m ∧
      mixedOptSuccess e.prob e.state = ∑ x, e.prob x * effectProb (m x) (e.state x) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P12

end
