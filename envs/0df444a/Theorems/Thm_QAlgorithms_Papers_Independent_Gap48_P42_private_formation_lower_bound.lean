-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P42_private_formation_lower_bound
-- name    : QAlgorithms.Papers.Independent.Gap48.P42.private_formation_lower_bound
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-22T05:37:35.935805+00:00
-- url     : https://prove2.me/theorems/3cc1dc67-a2db-497c-aa5a-72729e2361f6
-- title:
--   Private-dit entanglement of formation is at least the key size
-- statement:
--   Let $d,a,b$ be positive integers, let $\rho$ be a positive semidefinite trace-one shield state on $\mathbb C^a\otimes\mathbb C^b$, and let each $U_i$ be a unitary on that joint shield. Write
--
--   $$
--   \gamma^{(d)}=\frac1d\sum_{i,j=0}^{d-1}|ii\rangle\langle jj|\otimes U_i\rho U_j^\dagger,
--   $$
--
--   with the bipartition $AA':BB'$ and local shield dimensions $a,b$. All logarithms and resource rates are in bits.
--
--   Let $E_F$ denote the convex roof of the entropy of the Alice marginal, over all finite normalized pure-state ensembles representing the input state. Then
--
--   $$
--   E_F(\gamma^{(d)})\ge\log_2d.
--   $$
--
--   The case $d=1$ is included and gives the lower bound zero. This bounds the actual formation functional without an assumption that an optimal ensemble is supplied.
-- source:
--   Quantum states representing perfectly secure bits are always distillable, arXiv:quant-ph/0602176v2, PDF p. 4, III, Property 1 / Eq. (3.8)

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P42

namespace QAlgorithms.Papers.Independent.Gap48.P42

open scoped BigOperators Matrix ComplexConjugate ComplexOrder ENNReal

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.4, Property 1, Eq.(3.8): finite convex-roof formation across
AA' versus BB' is at least log_2 d, including d=1. -/
theorem private_formation_lower_bound {d a b : ℕ}
    (hd : 0 < d) (ha : 0 < a) (hb : 0 < b)
    (rho : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) (hrho : IsDensityMatrix rho)
    (U : Fin d → Matrix.unitaryGroup (Fin a × Fin b) ℂ) :
    Real.logb 2 d ≤ Information100.P08.formation (bipartitePrivate rho U) := by sorry

end

end QAlgorithms.Papers.Independent.Gap48.P42
