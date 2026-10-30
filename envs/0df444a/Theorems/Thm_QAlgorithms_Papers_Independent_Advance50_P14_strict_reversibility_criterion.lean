-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P14_strict_reversibility_criterion
-- name    : QAlgorithms.Papers.Independent.Advance50.P14.strict_reversibility_criterion
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T10:20:38.98901+00:00
-- url     : https://prove2.me/theorems/17ad7759-07b7-4857-b80a-88ea3644abe7
-- title:
--   Section V closing: strict reversibility criterion
-- statement:
--   All systems are finite-dimensional complex multipartite systems with at least two parties and positive local dimensions. Every state is positive semidefinite with trace one. Separability means a convex mixture of products across all parties. Logarithms are base two, and the trace norm has no factor of one half. Let $LG$ and $LH$ be the smoothed regularizations of logarithmic global and standard robustness, respectively: minimize over density approximations tending to the tensor powers in full trace norm, take the limsup of log robustness divided by positive blocklength, and then the infimum over approximation sequences. For every state $\rho$,
--
--   $$E_C^{\rm ne}(\rho)=E_D^{\rm ne}(\rho)\quad\Longleftrightarrow\quad LH(\rho)=LG(\rho).$$
--
--   This reduces the open strict-reversibility question to equality of two independently defined quantities. It asserts neither equality unconditionally and includes separable inputs.
-- source:
--   A reversible theory of entanglement and its relation to the second law, arXiv:0710.5827v3, PDF p. 16, Section V closing: strict reversibility criterion

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P14

noncomputable section

open Filter

open QAlgorithms.Papers.Independent.Claimed50.P33 (RegisterBasis)

open scoped Matrix ComplexOrder ENNReal NNReal

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Advance50.P14

/-- PDF p.16, closing reduction of an OPEN question: strict reversibility at
rho is equivalent to LH(rho)=LG(rho). Neither equality is asserted outright.
Separable states are included. -/
theorem strict_reversibility_criterion {m : ℕ} (A : MultipartiteRegister m) (rho : PartyOperator A)
    (hrho : IsDensityMatrix rho) :
    (asymptoticFormationCost .strict A rho = distillableEntanglement .strict A rho) ↔
      smoothedRegularizedRobustness true A rho =
        smoothedRegularizedRobustness false A rho := by sorry

end QAlgorithms.Papers.Independent.Advance50.P14

end
