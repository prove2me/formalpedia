-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P12_classical_reductions
-- name    : QAlgorithms.Papers.Independent.Advance50.P12.classical_reductions
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T10:19:56.854475+00:00
-- url     : https://prove2.me/theorems/21ef3e64-6c59-4b76-bf1b-2577ba4f7901
-- title:
--   §I C 2: classical reductions of the two operational quantities
-- statement:
--   All registers are finite-dimensional complex Hilbert spaces of positive dimension, represented in arbitrary orthonormal bases. States are positive semidefinite operators of trace one. All logarithms are binary, and $F(\rho,\sigma)=\|\sqrt\rho\sqrt\sigma\|_1$ denotes root fidelity. Conditional min-entropy optimizes the operator-order definition over every normalized reference state; conditional max-entropy is defined by purification duality.
--
--   For a finite normalized mixed ensemble $\{p_x,\rho_B^x\}_{x\in X}$, form the classical-quantum state $\rho_{XB}=\sum_xp_x|x\rangle\langle x|\otimes\rho_B^x$. Let $q_{\mathrm{corr}}$ be $|X|$ times the optimal squared fidelity with $|X|^{-1/2}\sum_x|x,x\rangle$, after any CPTP map $B\to X'$. Let $q_{\mathrm{decpl}}$ be $|X|\max_{\sigma_B}F(\rho_{XB},I_X/|X|\otimes\sigma_B)^2$. Then
--   $$q_{\mathrm{corr}}(X|B)_\rho=p_{\mathrm{guess}}(X|B)_\rho,\qquad q_{\mathrm{decpl}}(X|B)_\rho=p_{\mathrm{secr}}(X|B)_\rho.$$
--   Here $p_{\mathrm{guess}}$ optimizes $\sum_xp_x\operatorname{tr}(E_x\rho_B^x)$ over all POVMs, and $p_{\mathrm{secr}}$ optimizes $(\sum_x\sqrt{p_x}F(\rho_B^x,\sigma_B))^2$ over all density operators. These two reductions connect the quantum tasks to their classical specializations.
-- source:
--   The operational meaning of min- and max-entropy, arXiv:0807.1338v2, PDF p. 5, Section I C 2 (continued p.6)

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

/-- PDF pp.5–6, Section I C 2: both operational quantities specialize to
classical guessing and secrecy, with the same dimension scaling. -/
theorem classical_reductions [Nonempty X] [Nonempty B]
    (e : CQData X B) (he : e.Valid) :
    qCorr (cqDensity e) = mixedOptSuccess e.prob e.state ∧
    qDecpl (cqDensity e) = pSecr e := by sorry

end QAlgorithms.Papers.Independent.Advance50.P12

end
