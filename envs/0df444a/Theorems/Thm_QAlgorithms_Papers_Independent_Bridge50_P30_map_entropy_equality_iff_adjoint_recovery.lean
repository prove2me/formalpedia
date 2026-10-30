-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P30_map_entropy_equality_iff_adjoint_recovery
-- name    : QAlgorithms.Papers.Independent.Bridge50.P30.map_entropy_equality_iff_adjoint_recovery
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T18:33:06.951759+00:00
-- url     : https://prove2.me/theorems/84285145-64dc-491b-b1a8-bd6a846f9c92
-- title:
--   Map-entropy preservation is equivalent to superoperator adjoint recovery
-- statement:
--   Let $N\ge1$ and let $\Phi,\Psi$ be complex-linear completely positive trace-preserving maps on the operators on $\mathbb C^N$. Assume additionally that $\Phi(I)=I$; no identity-preservation hypothesis is imposed on $\Psi$. Fix the coordinate orthonormal basis, put $|\Omega\rangle=\sum_{i=1}^N|i\rangle\otimes|i\rangle$, and define the unnormalized, output-first Choi matrix $J(\Theta)=(\Theta\otimes\mathrm{id})(|\Omega\rangle\langle\Omega|)$. Define $S^{\mathrm{map}}(\Theta)=S(J(\Theta)/N)$, where $S$ is von Neumann entropy in bits, with $0\log_2 0=0$. If $\Phi^\dagger$ denotes the Hilbert–Schmidt adjoint, then
--
--   $$
--   S^{\mathrm{map}}(\Phi\circ\Psi)=S^{\mathrm{map}}(\Psi)
--   \quad\Longleftrightarrow\quad
--   \Phi^\dagger\circ\Phi\circ\Psi=\Psi.
--   $$
--
--   Equality on the right is equality on every operator. This characterizes preservation of the normalized Choi-state entropy under composition.
-- source:
--   Von Neumann Entropy-Preserving Quantum Operations, arXiv:1104.2992v4, PDF p. 4, Theorem 2.3

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P30

noncomputable section

open scoped BigOperators Matrix ComplexOrder

namespace QAlgorithms.Papers.Independent.Bridge50.P30

open QAlgorithms.Papers.Independent.Information100.P50
  (M Lin choiMatrix hilbertSchmidtAdjoint)

open QAlgorithms.Papers.Independent.Claimed50.P08 (classicalEntropy)

/-- PDF p.4, Theorem 2.3. Psi is trace-preserving and CP, with no unitality
assumption. Recovery holds on every operator, not only on one input state. -/
theorem map_entropy_equality_iff_adjoint_recovery
    {N : ℕ} (hN : 0 < N) (Phi Psi : Lin N N)
    (hPhi : IsBistochastic Phi) (hPsi : IsChannel Psi) :
    mapEntropy (Phi.comp Psi) = mapEntropy Psi ↔
      (fun X => hilbertSchmidtAdjoint Phi (Phi (Psi X))) = Psi.toFun := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P30

end
