-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier30_P14_swapPartialTraceIdentity
-- name    : QAlgorithms.Papers.Independent.Frontier30.P14.swapPartialTraceIdentity
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T09:23:49.41203+00:00
-- url     : https://prove2.me/theorems/2bf4e71e-c90e-4af9-af15-0e3713da6c14
-- title:
--   Swap and partial traces: corrected trace-class domain
-- statement:
--   Let $\Theta$ be a trace-class operator on the completed two-mode Fock space and let $\Xi$ be the self-adjoint vacuum-preserving swap. Then, as bounded operators,
--
--   $$\operatorname{Tr}_b(\Xi\Theta\Xi)\otimes I_b
--   =\Xi\bigl(I_a\otimes\operatorname{Tr}_a\Theta\bigr)\Xi.$$
--
--   The trace-class hypothesis corrects the printed assertion for arbitrary bounded $\Theta$: genuine partial traces are not defined for the infinite-dimensional identity. Tensoring the resulting bounded operators with identities is valid and does not require those identities to be trace class. The corrected identity is exactly the form applied to the evolved joint density in Appendix A.3.
-- source:
--   Degradability of Bosonic Gaussian channels, arXiv:quant-ph/0603257v4, PDF p. 6, Appendix A.3, (A14)

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P14

noncomputable section

open scoped BigOperators NNReal ENNReal

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33

open QAlgorithms.Papers.Independent.Dependency50.P39 (displacementMatrix)

namespace QAlgorithms.Papers.Independent.Frontier30.P14

/-- Appendix A.3 (A14), PDF p.6, corrected domain. Printed: any bounded Theta.
Changed: trace-class Theta, since genuine infinite-dimensional partial traces
are not defined on the identity. Tensoring the resulting bounded operators with
an identity is harmless; no claim that that identity is trace class is made.
This correction requires independent moderation. -/
theorem swapPartialTraceIdentity (Theta : (Matrix (ℕ × ℕ) (ℕ × ℕ) ℂ))
    (htrace : IsTraceClass Theta) :
    productCoeff (partialRight (swapCoefficients Theta)) (identityCoeff ℕ) =
      swapCoefficients (productCoeff (identityCoeff ℕ) (partialLeft Theta)) := by sorry

end QAlgorithms.Papers.Independent.Frontier30.P14

end
