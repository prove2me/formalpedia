-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P43_transpose_not_cp
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P43.transpose_not_cp
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T05:19:26.753252+00:00
-- url     : https://prove2.me/theorems/0e38e366-e981-4f43-bbf0-17a74a344971
-- title:
--   Transposition separates positivity and PPT preservation from complete positivity
-- statement:
--   All operators act on a finite bipartite space $\mathbb C^d\otimes\mathbb C^d$ in a fixed product basis. Write $\Gamma=T_2$ for Bob's partial transpose and $P_m=|\psi_m\rangle\langle\psi_m|$, where $|\psi_m\rangle=m^{-1/2}\sum_i|ii\rangle$. A density operator is positive semidefinite with complex trace exactly one. An admissible PPT map is complex-linear, positive and trace preserving, and $\Gamma_{\rm out}T\Gamma_{\rm in}$ is positive on every positive operator. A PPT channel is additionally completely positive; complete positivity of the transpose-conjugated map is not required. Fidelity means the overlap $\operatorname{tr}(P_m T(\rho))$.
--
--   Let $d\ge2$ and let $\Theta(X)=X^{\mathsf T}$ be full transposition on the bipartite matrix algebra. Then
--
--   $$\Theta\text{ is positive, trace preserving and PPT preserving},\qquad\Theta\text{ is not completely positive}.$$
--
--   This exhibits the distinction between admissible positive maps and channels. Full transposition here is complex-linear and does not conjugate the entries.
-- source:
--   Distillability via protocols respecting the positivity of partial transpose, arXiv:quant-ph/0104095v2, PDF p. 2, Counterexample before Theorem 1

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P43

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Intakethird100.P43

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P04
  (gamma copies bellProjector negativeProjector werner)

open QAlgorithms.Papers.Independent.Information100.P30 (IsPositiveMap)

/-- PDF p.2, paragraph before Theorem 1: full transposition is positive,
trace-preserving and PPT-preserving but not completely positive. d>=2 excludes scalars. -/
theorem transpose_not_cp (d : ℕ) (hd : 2 ≤ d) :
    IsPPTMap ((Matrix.transposeLinearEquiv (Fin d × Fin d) (Fin d × Fin d) ℂ ℂ).toLinearMap) ∧
      ¬ Entanglement.IsCompletelyPositive ((Matrix.transposeLinearEquiv (Fin d × Fin d) (Fin d × Fin d) ℂ ℂ).toLinearMap) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P43

end
