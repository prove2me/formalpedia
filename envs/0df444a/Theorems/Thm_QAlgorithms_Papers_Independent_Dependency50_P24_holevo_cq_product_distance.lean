-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P24_holevo_cq_product_distance
-- name    : QAlgorithms.Papers.Independent.Dependency50.P24.holevo_cq_product_distance
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T16:22:11.838179+00:00
-- url     : https://prove2.me/theorems/0a9fa87d-b177-4637-b5bd-43fc40fa9a7c
-- title:
--   Proposition 7: Holevo controls cq product norm
-- statement:
--   All spaces are finite dimensional and have positive dimension. A state means a positive semidefinite operator of trace one. The distinguished product basis $B$ is fixed and is used for both twisting and key measurement. Norms are full trace norms, fidelity $F$ is root fidelity, and logarithms are in bits.
--
--   For a finite normalized ensemble $(p_k,\rho_k)$ with average $\bar\rho$ and Holevo information $\chi$, and any $\epsilon\ge0$,
--
--   $$\chi\le\epsilon\ \Longrightarrow\ \left\|\sum_kp_k|k\rangle\langle k|\otimes\rho_k-\sum_kp_k|k\rangle\langle k|\otimes\bar\rho\right\|_1\le\sqrt{2\epsilon}.$$
--
--   This compares the cq state to the product of its actual marginals.
-- source:
--   General paradigm for distilling classical key from quantum states, arXiv:quant-ph/0506189v2, PDF p. 37, Proposition 7: Holevo controls cq product norm

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

/-- PDF p.37, Proposition 7, Eq.(259), visually checked: sqrt(2 epsilon). -/
theorem holevo_cq_product_distance {L H : Type*} [Fintype L] [Fintype H]
    [Nonempty L] [Nonempty H] (p : L → ℝ) (rho : L → Op H) (hensemble : IsEnsemble p rho)
    (eps : ℝ) (hpos : 0 ≤ eps) (hchi : ensembleHolevoBits p rho ≤ eps) :
    traceNorm (cqState p rho - cqProduct p rho) ≤ Real.sqrt (2*eps) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P24

end
