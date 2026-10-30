-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P12_classical_secrecy
-- name    : QAlgorithms.Papers.Independent.Advance50.P12.classical_secrecy
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T10:19:12.229204+00:00
-- url     : https://prove2.me/theorems/089279bc-7904-442d-b432-cec1be4df69c
-- title:
--   §I C 1 / (19): classical max-entropy is key secrecy
-- statement:
--   All registers are finite-dimensional complex Hilbert spaces of positive dimension, represented in arbitrary orthonormal bases. States are positive semidefinite operators of trace one. All logarithms are binary, and $F(\rho,\sigma)=\|\sqrt\rho\sqrt\sigma\|_1$ denotes root fidelity. Conditional min-entropy optimizes the operator-order definition over every normalized reference state; conditional max-entropy is defined by purification duality.
--
--   For a finite normalized mixed ensemble $\{p_x,\rho_B^x\}_{x\in X}$, allowing $p_x=0$, form $\rho_{XB}=\sum_xp_x|x\rangle\langle x|\otimes\rho_B^x$. Define its dimension-scaled secrecy by the ensemble expression
--   $$p_{\mathrm{secr}}(X|B)_\rho=\max_{\sigma_B\text{ state}}\left(\sum_x\sqrt{p_x}\,F(\rho_B^x,\sigma_B)\right)^2.$$
--   The maximum is attained and
--   $$p_{\mathrm{secr}}(X|B)_\rho=2^{H_{\max}(X|B)_\rho}.$$
--   This gives the fidelity-based security of a classical key with quantum side information. The reference state is freely optimized, and secrecy can reach $|X|$.
-- source:
--   The operational meaning of min- and max-entropy, arXiv:0807.1338v2, PDF p. 5, Section I C 1 / (19)

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

/-- PDF p.5, (19): secrecy of a classical key, with arbitrary normalized
reference state rather than only its actual marginal. -/
theorem classical_secrecy [Nonempty X] [Nonempty B]
    (e : CQData X B) (he : e.Valid) :
    ENNReal.ofReal (pSecr e) = exp2Extended (purificationMaxEntropy (cqDensity e)) ∧
    ∃ sigma : Matrix B B ℂ, IsDensityMatrix sigma ∧
      pSecr e = (∑ x, Real.sqrt (e.prob x) * rootFidelity (e.state x) sigma) ^ 2 := by sorry

end QAlgorithms.Papers.Independent.Advance50.P12

end
