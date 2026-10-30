-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P12_product_entropies
-- name    : QAlgorithms.Papers.Independent.Advance50.P12.product_entropies
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T10:22:34.255302+00:00
-- url     : https://prove2.me/theorems/bd1968fd-3937-4804-8e9d-6dd5980a1f0e
-- title:
--   §I A / (24): min- and max-entropy of product states
-- statement:
--   All registers are finite-dimensional complex Hilbert spaces of positive dimension, represented in arbitrary orthonormal bases. States are positive semidefinite operators of trace one. All logarithms are binary, and $F(\rho,\sigma)=\|\sqrt\rho\sqrt\sigma\|_1$ denotes root fidelity. Conditional min-entropy optimizes the operator-order definition over every normalized reference state; conditional max-entropy is defined by purification duality.
--
--   Let $\rho_A,\rho_B$ be any density operators and construct $\rho_{AB}=\rho_A\otimes\rho_B$. Write $\|\rho_A\|_\infty$ for its operator norm, equal to its largest eigenvalue. Then
--   $$H_{\min}(A|B)_\rho=-\log_2\|\rho_A\|_\infty,\qquad H_{\max}(A|B)_\rho=2\log_2\operatorname{tr}\sqrt{\rho_A}.$$
--   These formulas identify the product-state entropies with the order-infinity and order-one-half Renyi entropies. The final equation (24) is used; intermediate p.6 formulas omit necessary fidelity squares.
-- source:
--   The operational meaning of min- and max-entropy, arXiv:0807.1338v2, PDF p. 2, Section I A; (24) on p.6

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

/-- PDF p.2 and p.6, (24): both product-state spectral formulas.
Printed p.6 intermediate fidelity expressions omit squares; the statement uses
the final (24), consistently with (22)–(23). -/
theorem product_entropies [Nonempty A] [Nonempty B]
    (rhoA : Matrix A A ℂ) (ha : IsDensityMatrix rhoA)
    (rhoB : Matrix B B ℂ) (hb : IsDensityMatrix rhoB) :
    conditionalMinEntropy (Matrix.kronecker rhoA rhoB) = -elog (specNorm rhoA) ∧
    purificationMaxEntropy (Matrix.kronecker rhoA rhoB) = (2 : EReal) * elog ((cfc Real.sqrt rhoA).trace.re) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P12

end
