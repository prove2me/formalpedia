-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P99_nonlocalOrder_iff
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P99.nonlocalOrder_iff
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T09:48:35.78249+00:00
-- url     : https://prove2.me/theorems/df6a6e3c-618d-4098-a410-1d76c628f4d8
-- title:
--   Result 3: interaction-independent order in the restricted chamber
-- statement:
--   For a two-qubit unitary $U$, let $\beta$ be an actual interaction-content witness: $U$ is locally equivalent, up to global phase, to $U_\beta=\exp[-i\sum_{k=1}^3\beta_k\sigma_k\otimes\sigma_k]$, where $\sigma_1,\sigma_2,\sigma_3$ are the Pauli matrices $X,Y,Z$ and $\pi/4\ge\beta_1\ge\beta_2\ge|\beta_3|$. For real triples, $x\prec_s y$ means s-majorization: sort their absolute coordinates in descending order, give the smallest coordinate the sign of the product, and compare the first coordinate and the two sums $x_1+x_2\mp x_3$. Let $V$ have canonical content $\beta^V$, and write $\beta^U=\beta$ for that of $U$. Assume $\beta^U_1+|\beta^U_3|\le\pi/4$ and $\beta^V_1+|\beta^V_3|\le\pi/4$. With interaction cost in the ideal free-local-control model, define $U$ to be more nonlocal than $V$ when $C_H(V)\le C_H(U)$ for every Hermitian two-qubit Hamiltonian $H$. Then
--
--   $$[\,\forall H,\ C_H(V)\le C_H(U)\,]\quad\Longleftrightarrow\quad\beta^V\prec_s\beta^U.$$
--
--   The comparison is a preorder on gates and descends to local-equivalence classes. Local gates are included.
-- source:
--   Characterization of non-local gates, arXiv:quant-ph/0205100v3, PDF p. 8, Result 3: interaction-independent order in the restricted chamber

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P99

namespace QAlgorithms.Papers.Independent.Intakethird100.P99

open scoped Matrix Kronecker NNReal ENNReal

open QAlgorithms.Papers.Independent.Information100.P10 (pauli)

open QAlgorithms.Papers.Independent.Information100.P32 (evolution)

noncomputable section

/-- PDF p.8, Result 3 (definition pp.7–8): both contents must lie in the restricted
chamber. Includes local gates without the proof's invalid C_H(U)=1 shortcut there. -/
theorem nonlocalOrder_iff (U V : TwoMatrix) (bU bV : Triple)
    (hU : HasContent U bU) (hV : HasContent V bV)
    (hRU : bU 0 + |bU 2| ≤ Real.pi / 4) (hRV : bV 0 + |bV 2| ≤ Real.pi / 4) :
    MoreNonlocal U V ↔ SMajorized bV bU := by sorry

end

end QAlgorithms.Papers.Independent.Intakethird100.P99
