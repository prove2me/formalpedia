-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P43_linear_processor_cost
-- name    : QAlgorithms.Papers.Independent.Extend50.P43.linear_processor_cost
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T21:01:17.609414+00:00
-- url     : https://prove2.me/theorems/8931838d-0a61-4acb-9e22-d543f647d57c
-- title:
--   Uniform linear size of the supplied-program processor
-- statement:
--   Count a two-qubit Bell measurement with its four-valued readout as a fixed primitive operation, equivalently any fixed elementary realization at constant cost. For each $m\geq1$, let $\mathcal C_m$ be the fixed list measuring $(A_1,B_1),\ldots,(A_m,B_m)$, with register $C$ designated as output. Let $s(\mathcal C_m)$ be the actual list length. There is an absolute constant $C_0>0$ such that, uniformly over $m$, every unitary $U$ and every normalized data input $d$,
--
--   $$
--   s(\mathcal C_m)\leq C_0m,\qquad
--   \rho_{C,o_+}=2^{-2m}|Ud\rangle\langle Ud|,\qquad \operatorname{Tr}\rho_{C,o_+}=2^{-2m}.
--   $$
--
--   Here the input is $d_A\otimes P_U$ with the Eq.(11) supplied program; $\rho_{C,o_+}$ is the actual unnormalized output obtained by executing the listed Bell projectors and tracing out $A,B$. Readout is included. The bound excludes preparing $P_U$ and repeating failed attempts, and expresses the source's linear cost without attributing an elementary-gate constant to it.
-- source:
--   Programmable quantum gate arrays, arXiv:quant-ph/9703032v1, PDF p. 3, Unnumbered main resource bound: linear size of the supplied-program processor

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P43

namespace QAlgorithms.Papers.Independent.Extend50.P43

open scoped ComplexConjugate

noncomputable section

/-- PDF p.3, linear gate-operation claim (construction on p.2): a universal
constant bounds the actual supplied-program processor size linearly in m.
Bell readout is counted as a fixed two-qubit primitive and C is the allowed
output register. The execution semantics retain the exact successful output
and probability. Program preparation and repetitions are outside this bound. -/
theorem linear_processor_cost :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m →
      ((fixedProcessor m).length : ℝ) ≤ C * (m : ℝ) ∧
      ∀ U : Matrix (Qubits m) (Qubits m) ℂ,
        U ∈ Matrix.unitaryGroup (Qubits m) ℂ →
        ∀ d : EuclideanSpace ℂ (Qubits m), IsState d →
          processorOutputDensity (fixedProcessor m) (successOutcome m)
              (tensorVec d (program U)) =
            ((2 : ℂ) ^ (2 * m))⁻¹ • pureDensity (act U d) ∧
          (processorOutputDensity (fixedProcessor m) (successOutcome m)
              (tensorVec d (program U))).trace.re =
            ((2 : ℝ) ^ (2 * m))⁻¹ := by sorry

end

end QAlgorithms.Papers.Independent.Extend50.P43
