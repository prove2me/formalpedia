-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P24_cq_security_implications
-- name    : QAlgorithms.Papers.Independent.Dependency50.P24.cq_security_implications
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T16:20:31.409983+00:00
-- url     : https://prove2.me/theorems/5362cd7b-4cb7-4ff4-b824-d7be2822e72c
-- title:
--   Lemma 8: three cq security implications, corrected square root
-- statement:
--   All spaces are finite dimensional and have positive dimension. A state means a positive semidefinite operator of trace one. The distinguished product basis $B$ is fixed and is used for both twisting and key measurement. Norms are full trace norms, fidelity $F$ is root fidelity, and logarithms are in bits.
--
--   Let $(p_k,\rho_k)$ be a finite normalized ensemble, let $\bar\rho=\sum_kp_k\rho_k$, $\Omega=\sum_kp_k|k\rangle\langle k|\otimes\rho_k$, and $\Pi=\sum_kp_k|k\rangle\langle k|\otimes\bar\rho$. For $0<\epsilon\le1/2$ the three implications are
--
--   $$\|\Omega-\Pi\|_1\le\epsilon\Rightarrow\sum_kp_kF(\rho_k,\bar\rho)\ge1-\epsilon/2,$$
--   $$\sum_kp_kF(\rho_k,\bar\rho)\ge1-\epsilon\Rightarrow\sum_kp_k\|\rho_k-\bar\rho\|_1\le\sqrt{8\epsilon},$$
--   $$\sum_kp_k\|\rho_k-\bar\rho\|_1\le\epsilon\Rightarrow\|\Omega-\Pi\|_1\le\epsilon.$$
--
--   They compare security criteria with the corrected square-root estimate supplied by Eq.(241).
-- source:
--   General paradigm for distilling classical key from quantum states, arXiv:quant-ph/0506189v2, PDF p. 35, Lemma 8: three cq security implications, corrected square root

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P24

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P24

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

open Finset

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

-- Accepted declarations are imported rather than redeclared locally.

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P04 (bellProjector)

open QAlgorithms.Papers.Independent.Information100.P07 (positivePart negativePart)

open QAlgorithms.Papers.Independent.Information100.P34 (supportProjector)

open QAlgorithms.Papers.Independent.Information100.P54 (relativeEntropyBits relativeEntanglement)

/-- PDF pp.35–36, Lemma 8: (232),(242) print the false linear bound 8 epsilon.
Use sqrt(8 epsilon), supplied by (241). Retain all three implications and root fidelity. -/
theorem cq_security_implications {L H : Type*} [Fintype L] [Fintype H]
    [Nonempty L] [Nonempty H] (p : L → ℝ) (rho : L → Op H) (hensemble : IsEnsemble p rho)
    (eps : ℝ) (hpos : 0 < eps) (hsmall : eps ≤ 1/2) :
    (traceNorm (cqState p rho - cqProduct p rho) ≤ eps → ensembleMeanRootFidelity p rho ≥ 1-eps/2) ∧
    (ensembleMeanRootFidelity p rho ≥ 1-eps → meanDistance p rho ≤ Real.sqrt (8*eps)) ∧
    (meanDistance p rho ≤ eps → traceNorm (cqState p rho - cqProduct p rho) ≤ eps) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P24

end
