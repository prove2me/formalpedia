-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P30_entropy_equality_iff_adjoint_recovery
-- name    : QAlgorithms.Papers.Independent.Bridge50.P30.entropy_equality_iff_adjoint_recovery
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T18:32:19.35118+00:00
-- url     : https://prove2.me/theorems/b8d2f928-4138-492c-b391-c5bdf37ae53d
-- title:
--   Entropy preservation is equivalent to Hilbert–Schmidt adjoint recovery
-- statement:
--   Let $N\ge 1$, let $\rho$ be a positive semidefinite operator of trace one on $\mathbb C^N$, and let $\Phi$ be a complex-linear, completely positive, trace-preserving and identity-preserving map on its operators. Write $S(\rho)=-\operatorname{Tr}(\rho\log_2\rho)$, with zero eigenvalues contributing zero, and let $\Phi^\dagger$ be the Hilbert–Schmidt adjoint, defined by $\operatorname{Tr}(\Phi(X)^\dagger Y)=\operatorname{Tr}(X^\dagger\Phi^\dagger(Y))$. Then
--
--   $$
--   S(\Phi(\rho))=S(\rho)\quad\Longleftrightarrow\quad\Phi^\dagger(\Phi(\rho))=\rho.
--   $$
--
--   This characterizes entropy preservation at an arbitrary, possibly singular, state by recovery using the computed adjoint of the given channel.
-- source:
--   Von Neumann Entropy-Preserving Quantum Operations, arXiv:1104.2992v4, PDF p. 3, Theorem 2.1(i) iff (ii)

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P30

noncomputable section

open scoped BigOperators Matrix ComplexOrder

namespace QAlgorithms.Papers.Independent.Bridge50.P30

open QAlgorithms.Papers.Independent.Information100.P50
  (M Lin choiMatrix hilbertSchmidtAdjoint)

open QAlgorithms.Papers.Independent.Claimed50.P08 (classicalEntropy)

/-- PDF p.3, Theorem 2.1(i) iff (ii), including its independent proof on that page.
No structural clause (iii) is asserted. Singular density matrices are allowed. -/
theorem entropy_equality_iff_adjoint_recovery
    {N : ℕ} (hN : 0 < N) (rho : M N) (Phi : Lin N N)
    (hrho : IsDensityMatrix rho) (hPhi : IsBistochastic Phi) :
    vnEntropy (Phi rho) = vnEntropy rho ↔
      hilbertSchmidtAdjoint Phi (Phi rho) = rho := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P30

end
