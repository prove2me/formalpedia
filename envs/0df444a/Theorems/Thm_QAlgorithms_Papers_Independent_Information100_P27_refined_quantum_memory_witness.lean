-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P27_refined_quantum_memory_witness
-- name    : QAlgorithms.Papers.Independent.Information100.P27.refined_quantum_memory_witness
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T10:18:27.166099+00:00
-- url     : https://prove2.me/theorems/8696ce74-2660-43a8-8d33-210152a19a7e
-- title:
--   §9.1 and Appendix D.6: improved rational feasible witness
-- statement:
--   Fix the symmetric qubit source $p=1/2$, dephasing parameter $\gamma=4/5$, and $\mu=1$. Write $h_2$ for binary entropy in bits, $b(q,t)=h_2((1+\sqrt{(2q-1)^2+4q(1-q)t^2})/2)$, and $F_\mu(q,t)=h_2(q)+\mu b(q,t)-(1+\mu)b(q,\gamma t)$. For $t\in\{223/250,9/10\}$, the memory vectors $f_0=(1,0)$ and $f_1=(t,\sqrt{1-t^2})$ are unit vectors and $V_t|i\rangle=|i\rangle|f_i\rangle$ is an isometry. Its feasible matrix has entries $\theta_{ij}=\langle f_j|f_i\rangle/2$, is a density matrix with diagonal $(1/2,1/2)$, and its matrix entropy objective equals $F_1(1/2,t)$. In particular,
--
--   $$
--   F_1(1/2,223/250)=1+h_2(473/500)-2h_2(1071/1250)
--   >1+h_2(19/20)-2h_2(43/50)=F_1(1/2,9/10).
--   $$
--
--   This is a strict improvement between two explicit feasible instruments, without a global optimality assertion.
-- source:
--   Static classical-quantum- entanglement trade-offs: an entropic converse and single-letter characterizations, arXiv:2609.23298v1, PDF p. 43, §9.1 and Appendix D.6: improved rational feasible witness

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P27

noncomputable section

open scoped ComplexConjugate ComplexOrder

attribute [local instance] Classical.decEq Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Information100.P27

/-- arXiv:2609.23298v1 PDF pp.43-44, (9.17), certified on p.74: strict
improvement between two feasible matrix witnesses, with no optimum assertion. -/
theorem refined_quantum_memory_witness :
    (∀ t ∈ ({(223/250 : ℝ), (9/10 : ℝ)} : Set ℝ),
      (∀ i, IsState (witnessMemory t i)) ∧
      Matrix.conjTranspose (witnessInstrument t) * witnessInstrument t = 1 ∧
      (∀ i j, qubitTheta (1/2) t i j =
        (1/2 : ℂ) * inner ℂ (witnessMemory t j) (witnessMemory t i)) ∧
      matrixScore 1 (!![(1 : ℂ), (4/5 : ℂ); (4/5 : ℂ), (1 : ℂ)])
        (qubitTheta (1/2) t) = qubitScore (4/5) 1 (1/2) t) ∧
    IsDensityMatrix (qubitTheta (1/2) (223/250)) ∧
    IsDensityMatrix (qubitTheta (1/2) (9/10)) ∧
    (∀ i : Fin 2, (qubitTheta (1/2) (223/250)) i i = (1/2 : ℂ)) ∧
    qubitScore (4/5) 1 (1/2) (223/250) =
      1 + binEntropy2 (473/500) - 2 * binEntropy2 (1071/1250) ∧
    qubitScore (4/5) 1 (1/2) (9/10) =
      1 + binEntropy2 (19/20) - 2 * binEntropy2 (43/50) ∧
    qubitScore (4/5) 1 (1/2) (9/10) < qubitScore (4/5) 1 (1/2) (223/250) := by sorry

end QAlgorithms.Papers.Independent.Information100.P27

end
