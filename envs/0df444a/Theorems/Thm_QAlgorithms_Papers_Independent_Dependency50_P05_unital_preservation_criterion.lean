-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P05_unital_preservation_criterion
-- name    : QAlgorithms.Papers.Independent.Dependency50.P05.unital_preservation_criterion
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T07:55:24.160987+00:00
-- url     : https://prove2.me/theorems/74d49f9c-449f-4153-a1b4-7952e2278caa
-- title:
--   Ordinary unital-channel preservation with normalized affine criterion
-- statement:
--   All systems are finite dimensional complex Hilbert spaces with strictly positive input and output dimensions. A system $A$ comprises $A_0,A_1$. Channels are complex-linear CPTP maps on all operators, and a superchannel is completely CP-preserving and trace-preserving-map preserving. Its complete extension includes both registers of every auxiliary dynamical system. Write $J_\Theta$ for the unnormalized, input-first supermap Choi matrix, $J^S$ for its ordinary partial-trace marginal, and $u^S=I^S/d_S$. Tensor formulas use the named register order. Assume $d_{A_0}=d_{A_1}$ and $d_{B_0}=d_{B_1}$. For a superchannel $\Theta$, taking every random-unitary channel to a unital channel is equivalent to taking every unital channel to a unital channel. Furthermore, this is equivalent to the existence of Hermitian matrices $\alpha^{A_1B_1}$ and $\beta^{A_0B_1}$ such that
--   $$J^{AB_1}=I^{A_0}\otimes\alpha^{A_1B_1}+I^{A_1}\otimes\beta^{A_0B_1},\qquad J^{B_1}=d_{A_0}I^{B_1}.$$
--   Here unital means $\Phi(I)=I$, and register factors are placed in the named order. The normalization is the one established by the uniform-channel test immediately before the printed criterion.
-- source:
--   Comparison of Quantum Channels by Superchannels, arXiv:1808.02607v3, PDF p. 11, Sec. III-D, Eq.(58) and following criterion

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P05

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Dependency50.P05

local notation "Mat" I:max => Matrix I I ℂ

/-- arXiv:1808.02607v3, PDF p.11, Sec.III-D, Eq.(58) and following criterion.
Printed: the final iff gives only the affine decomposition. Changed: also require
J^{B1}=d_A0 I, from the uniform-channel instance of Eq.(58). Why: a fixed non-unital
replacer satisfies the decomposition alone. This correction was independently checked in round 1. -/
theorem unital_preservation_criterion {A B : System} (ha : A.input = A.output)
    (hb : B.input = B.output) (T : Supermap A B) (hT : IsSuperchannel T) :
    ((∀ X : Mat (ChoiRegister A), RandomUnitaryChannel A X → Unital (T X)) ↔ UnitalPreserving T) ∧
    (UnitalPreserving T ↔ AffineUnitalCriterion T) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P05

end
