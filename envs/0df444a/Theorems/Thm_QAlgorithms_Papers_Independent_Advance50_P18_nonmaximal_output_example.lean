-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P18_nonmaximal_output_example
-- name    : QAlgorithms.Papers.Independent.Advance50.P18.nonmaximal_output_example
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-29T11:47:40.317322+00:00
-- url     : https://prove2.me/theorems/c30ffa9e-384f-4fbf-b8e1-62311f6c0f1d
-- title:
--   §4, unnumbered example: a nonmaximally mixed private output
-- statement:
--   For one qubit, let $S=\{|0\rangle,|+\rangle\}$, where $|+\rangle=(|0\rangle+|1\rangle)/\sqrt2$. Take probabilities $p_1=p_2=1/2$ and unitaries $U_1=I$, $U_2=H$, where $H$ is the Hadamard matrix. This is an ancilla-free private quantum channel with fixed output
--
--   $$\rho_0=\begin{pmatrix}3/4&1/4\\1/4&1/4\end{pmatrix}\ne I_2/2.$$
--
--   Both source vectors therefore give this exact same averaged output, and each keyed encoding is invertible. The exhibited matrix shows that private outputs need not be maximally mixed.
-- source:
--   Private Quantum Channels and the Cost of Randomizing Quantum Information, arXiv:quant-ph/0003101v2, PDF p. 5, §4, unnumbered example: a nonmaximally mixed private output

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P18

namespace QAlgorithms.Papers.Independent.Advance50.P18

open scoped ComplexConjugate

noncomputable section

variable {K I A : Type*} [Fintype K] [DecidableEq K]
  [Fintype I] [DecidableEq I] [Fintype A] [DecidableEq A]

/-- PDF p.5, unnumbered example: the specified identity/Hadamard ensemble has
fixed output [[3/4,1/4],[1/4,1/4]], which is not maximally mixed. -/
theorem nonmaximal_output_example :
    BarePQC exampleSource exampleEnsemble hadamardExampleDensity ∧
      hadamardExampleDensity ≠ sourceMixedIdentity Bool := by sorry

end

end QAlgorithms.Papers.Independent.Advance50.P18
