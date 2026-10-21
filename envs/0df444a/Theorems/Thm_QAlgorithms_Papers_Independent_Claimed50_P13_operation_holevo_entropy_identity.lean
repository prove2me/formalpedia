-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P13_operation_holevo_entropy_identity
-- name    : QAlgorithms.Papers.Independent.Claimed50.P13.operation_holevo_entropy_identity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T09:41:30.393923+00:00
-- url     : https://prove2.me/theorems/bae2a791-d81d-4607-8830-3b1a2f2afbb3
-- title:
--   Section 6 unnumbered quantum-operation formula (37)
-- statement:
--   All systems are nonzero separable complex Hilbert spaces. States are positive trace-class operators of trace one, channels are complex-linear completely positive trace-preserving maps on the full trace class, and all logarithms are natural. Let $\Phi$ be a completely positive complex-linear trace-nonincreasing operation, and let $\mu$ be a probability ensemble of input states. Set $S(A)=-\operatorname{Tr}A\log A$ and $\overline\rho=\int\rho\,d\mu$. If $S(\Phi(\overline\rho))<\infty$, then
--
--   $$\chi_\Phi(\mu)+\int S(\Phi(\rho))\,\mu(d\rho)=S(\Phi(\overline\rho)).$$
--
--   This gives the entropy-difference formula on subnormalized outputs of an arbitrary quantum operation.
-- source:
--   On the entanglement-assisted classical capacity of infinite-dimensional quantum channels, arXiv:1210.6926v2, PDF p. 20, Section 6 unnumbered quantum-operation formula (37)

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P13

noncomputable section

open MeasureTheory Filter

open scoped ENNReal NNReal Topology BigOperators

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33

namespace QAlgorithms.Papers.Independent.Claimed50.P13

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Quantum-operation identity (37), PDF p.21, in ADDITIVE equivalent form with
finite average-output S. The nonnegative integral avoids default Bochner values.
All S terms mean -Tr A log A, not homogeneous H. -/
theorem operation_holevo_entropy_identity {I J : Type}
    [Countable I] [Countable J] [Nonempty I] [Nonempty J]
    (Phi : TraceDecreasingOperation I J) (mu : Ens.GeneralizedEnsemble I)
    (hfinite : subnormalizedS (Phi.val (Ens.averageCoefficients mu)) < ⊤) :
    Ens.ensembleHolevo Phi.val mu +
      (∫⁻ rho : State I, subnormalizedS (Phi.val rho.coefficients)
        ∂(mu : Measure (State I))) =
      subnormalizedS (Phi.val (Ens.averageCoefficients mu)) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P13

end
