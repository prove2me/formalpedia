-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P52_exact_ladder_contraction_polynomial_arithmetic
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P52.exact_ladder_contraction_polynomial_arithmetic
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T23:44:27.976951+00:00
-- url     : https://prove2.me/theorems/b3a423fa-3a95-427b-bdcf-1193b7fa7e7c
-- title:
--   §6.2: exact ladder contraction with polynomial arithmetic work
-- statement:
--   Take $n=m+1\ge1$ sites initially in $|0^n\rangle$, with arbitrary two-qubit unitaries $U_{i,i+1}$ applied in increasing site order. Choose any subset of measured sites and a normalized selected measurement ket at each site. Scan the ladder using $\sigma_{i,i+1}=U_{i,i+1}(\rho_i\otimes|0\rangle\langle0|)U_{i,i+1}^\dagger$, then either trace out site $i$ or contract its selected bra; apply the analogous trace or bra at the final site. If $p_{\mathrm{scan}}$ is its resulting real scalar and $F$ is the tensor product of the selected projectors and the unmeasured identities, then
--
--   $$ p_{\mathrm{scan}}=\operatorname{Tr}(F|\Phi_n\rangle\langle\Phi_n|). $$
--
--   There are universal natural constants $C>0,d$ such that, for each $n$ and measured subset, a valid scalar straight-line program of at most $Cn^d$ instructions computes this value for every choice of unitary and ket entries. The program is chosen before those entries. Its operations are input reads, constants, addition, multiplication and conjugation, with only earlier registers referenced. The scan uses only one- and two-site intermediate matrices. This is exact arithmetic work with precision ignored, and does not assert an exact finite-bit sampler.
-- source:
--   An introduction to measurement based quantum computation, arXiv:quant-ph/0508124v2, PDF p. 14, §6.2: exact ladder contraction with polynomial arithmetic work

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P52

noncomputable section

open scoped Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Intakenext100.P52

open QAlgorithms.Papers.Independent.Information100.P21 (Vec)

open QAlgorithms.Papers.Independent.Gap20.P01 (applyRect)

/-- Exact ladder contraction, PDF pp.14–15: the scan equals the joint Born
probability and is implementable by polynomially many scalar operations.
Constants and program selection precede gate and basis entries. n=m+1 includes
the one-site/no-gate case. Precision and finite-bit sampling are not asserted. -/
theorem exact_ladder_contraction_polynomial_arithmetic :
    ∃ C d : ℕ, 0 < C ∧ ∀ (m : ℕ) (measured : Fin (m+1) → Bool),
      ∃ program : ScalarProgram (LadderScalarInput m),
        program.Valid ∧ program.word.length ≤ C * (m+1)^d ∧
        ∀ (U : Fin m → Matrix QubitPair QubitPair ℂ),
          (∀ t, U t ∈ Matrix.unitaryGroup QubitPair ℂ) →
          ∀ (v : Fin (m+1) → Vec Bool), (∀ i, IsState (v i)) →
            ladderScanProbability U measured v =
              effectProb (ladderEvent measured v) (pureDensity (ladderState m U)) ∧
            (program.eval (ladderScalarData U v)).re = ladderScanProbability U measured v := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P52

end
