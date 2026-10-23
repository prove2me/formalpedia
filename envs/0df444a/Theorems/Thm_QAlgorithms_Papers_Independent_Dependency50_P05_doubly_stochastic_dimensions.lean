-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P05_doubly_stochastic_dimensions
-- name    : QAlgorithms.Papers.Independent.Dependency50.P05.doubly_stochastic_dimensions
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T07:52:30.756696+00:00
-- url     : https://prove2.me/theorems/3591bce3-ce14-4188-bc96-0ca02351e16a
-- title:
--   Dimension constraint for doubly stochastic superchannels
-- statement:
--   All systems are finite dimensional complex Hilbert spaces with strictly positive input and output dimensions. A system $A$ comprises $A_0,A_1$. Channels are complex-linear CPTP maps on all operators, and a superchannel is completely CP-preserving and trace-preserving-map preserving. Its complete extension includes both registers of every auxiliary dynamical system. Write $J_\Theta$ for the unnormalized, input-first supermap Choi matrix, $J^S$ for its ordinary partial-trace marginal, and $u^S=I^S/d_S$. Tensor formulas use the named register order. If both $\Theta$ and its Hilbert–Schmidt dual are superchannels, then
--   $$d_{A_0}d_{B_1}=d_{B_0}d_{A_1}.$$
--   Since all dimensions are positive, this is precisely $d_{A_0}/d_{A_1}=d_{B_0}/d_{B_1}$. Separate equality of input dimensions or output dimensions is not assumed. The constraint follows the source's notion of double stochasticity.
-- source:
--   Comparison of Quantum Channels by Superchannels, arXiv:1808.02607v3, PDF p. 8, Remark 1, Eq.(47)

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P05

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Dependency50.P05

local notation "Mat" I:max => Matrix I I ℂ

/-- arXiv:1808.02607v3, PDF pp.8–9, Remark 1, Eq.(47). Cross multiplication is legitimate
because every System has strictly positive input/output dimensions. -/
theorem doubly_stochastic_dimensions {A B : System} (T : Supermap A B)
    (hT : IsDoublyStochastic T) : A.input * B.output = B.input * A.output := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P05

end
