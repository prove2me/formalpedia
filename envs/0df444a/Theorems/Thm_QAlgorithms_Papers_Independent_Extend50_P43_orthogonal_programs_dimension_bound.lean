-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P43_orthogonal_programs_dimension_bound
-- name    : QAlgorithms.Papers.Independent.Extend50.P43.orthogonal_programs_dimension_bound
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T20:58:17.710176+00:00
-- url     : https://prove2.me/theorems/38c6033e-0244-4488-802b-1bb2f8201993
-- title:
--   Orthogonal programs and the program-dimension lower bound
-- statement:
--   Let $m,n\geq0$ and $N\geq1$ be integers. Let $G$ be one fixed unitary on an $m$-qubit data register and an $n$-qubit program register. For each $i\in\{1,\ldots,N\}$, let $U_i$ be a unitary on the data register and let $P_i$ be a normalized program that implements $U_i$ exactly: for every normalized data vector $d$, there is a normalized residual program $q_{i,d}$ with $G(d\otimes P_i)=U_id\otimes q_{i,d}$. Suppose no two $U_i$ differ by multiplication by a complex scalar of modulus one. Then
--
--   $$
--   \langle P_i,P_j\rangle=0\quad(i\ne j),\qquad N\leq 2^n,\qquad \log_2 N\leq n.
--   $$
--
--   Thus every distinct exact operation, modulo global phase, consumes an orthogonal program direction. The residual program's independence of $d$ is not assumed.
-- source:
--   Programmable quantum gate arrays, arXiv:quant-ph/9703032v1, PDF p. 2, Result: orthogonal programs and program-register dimension bound

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P43

namespace QAlgorithms.Papers.Independent.Extend50.P43

open scoped ComplexConjugate

noncomputable section

/-- PDF p.2, Result (model on p.1): programs for pairwise phase-inequivalent
unitaries are orthogonal; N such operations require dimension at least N,
or at least log₂ N program qubits. The positive-N hypothesis guards the log. -/
theorem orthogonal_programs_dimension_bound (m n N : ℕ) (hN : 1 ≤ N)
    (G : Matrix (Qubits m × Qubits n) (Qubits m × Qubits n) ℂ)
    (hG : G ∈ Matrix.unitaryGroup (Qubits m × Qubits n) ℂ)
    (U : Fin N → Matrix (Qubits m) (Qubits m) ℂ)
    (hU : ∀ i, U i ∈ Matrix.unitaryGroup (Qubits m) ℂ)
    (hDistinct : Pairwise (fun i j => ¬ ExactPhaseEquivalent (U i) (U j)))
    (P : Fin N → EuclideanSpace ℂ (Qubits n))
    (hImplements : ∀ i, ImplementsProgramUnitary G (U i) (P i)) :
    (∀ i j, i ≠ j → inner ℂ (P i) (P j) = 0) ∧
      N ≤ 2 ^ n ∧ Real.log (N : ℝ) / Real.log 2 ≤ (n : ℝ) := by sorry

end

end QAlgorithms.Papers.Independent.Extend50.P43
