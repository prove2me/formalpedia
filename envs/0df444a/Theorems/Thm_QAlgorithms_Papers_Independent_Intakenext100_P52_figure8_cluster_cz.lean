-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P52_figure8_cluster_cz
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P52.figure8_cluster_cz
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T23:41:15.744363+00:00
-- url     : https://prove2.me/theorems/9c45380e-45f5-47ed-bbfb-18f7b5559488
-- title:
--   §5 Figure 8: cluster pattern for CZ
-- statement:
--   Prepare a $4\times3$ rectangular cluster with an arbitrary normalized two-qubit input replacing $|+\rangle$ at the top-left and bottom-left sites. The top and bottom rows use the pattern $X,X,\mathrm{output}$; each middle row uses $X,Z,Z$. All grid entangling gates precede the measurements. There is a correction rule from the ten measured bits to two Paulis, selected before the input, such that
--
--   $$ |b_s\rangle\langle b_s|=\|b_s\|^2|\chi_s\rangle\langle\chi_s|,\qquad |\chi_s\rangle=(P_1(s)\otimes P_2(s))CZ|\psi\rangle. $$
--
--   Here $b_s$ is the actual contracted vector at the top-right and bottom-right outputs, in that order. This identifies every nonzero conditional quantum output up to phase and includes zero branches without assuming uniform outcome probabilities.
-- source:
--   An introduction to measurement based quantum computation, arXiv:quant-ph/0508124v2, PDF p. 11, §5 Figure 8: cluster pattern for CZ

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P52

noncomputable section

open scoped Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Intakenext100.P52

open QAlgorithms.Papers.Independent.Information100.P21 (Vec)

open QAlgorithms.Papers.Independent.Gap20.P01 (applyRect)

/-- Fig.8, PDF p.11: a fixed outcome-only Pauli correction works for every
normalized two-qubit input. Quantum branches, rather than just Z marginals,
are compared. Zero branches are included as zero subnormalized densities. -/
theorem figure8_cluster_cz :
    ∃ correction : (Figure8Measured → Bool) → (QubitPair × QubitPair),
      ∀ (psi : Vec QubitPair), IsState psi → ∀ s : Figure8Measured → Bool,
        let f := correction s
        let v := figure8Branch s psi
        pureDensity v = (‖v‖ ^ 2 : ℝ) • pureDensity
          (act (Matrix.kronecker (pauliByproduct f.1.1 f.1.2) (pauliByproduct f.2.1 f.2.2) * controlled pauliZ) psi) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P52

end
