-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P01_encodedAnalysis_coupling_inverse
-- name    : QAlgorithms.Papers.Independent.Renew46.P01.encodedAnalysis_coupling_inverse
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T19:44:04.177587+00:00
-- url     : https://prove2.me/theorems/9fcf0b9f-a158-4b0c-a3ab-a3cb9c1bec55
-- title:
--   Encoded analysis and physical coupling are inverse on their appropriate spaces
-- statement:
--   Let $n\ge2$. Let $S$ be the physical Schur synthesis matrix whose columns are the vectors in (B1), indexed by all admissible sequential spin paths and root projections, including all multiplicities. Fix the explicit binary encoding of these labels, using width $\lceil\log_2(n+1)\rceil$ for every label register, and let $E$ include valid labels into the resulting padded computational coordinates.
--
--   Define coupling $C=SE^\dagger$, encoded analysis $A=ES^\dagger$, and the valid-code projector $\Pi=EE^\dagger$. Then
--
--   $$
--   CA=I_{\mathrm{physical}},\qquad AC=\Pi_{\mathrm{valid\ code}}.
--   $$
--
--   These matrix identities specify the action on every superposition. Coupling and analysis are inverses on the physical and valid-code spaces, while invalid padded coordinates are projected away. This distinguishes the mathematical encoded-analysis isometry from physical clean Schur synthesis.
-- source:
--   Generalised Coupling and An Elementary Algorithm for the Quantum Schur Transform, arXiv:2305.04069v3, PDF p. 28, Appendix B, Eqs.(B2)–(B4): coupling is inverse to encoded analysis

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P01

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P01

open scoped BigOperators ComplexConjugate

attribute [local instance] Classical.propDecidable

/-- PDF pp.27--28, Appendix B, (B2)--(B4): analysis is inverse to
coupling on the physical/valid-code spaces. On the ambient padded space,
analysis after coupling is the valid-code projector, not the identity.
The concrete rectangular matrix equalities also specify the action on
all linear combinations, without selecting a unitary ghost completion. -/
theorem encodedAnalysis_coupling_inverse (n : ℕ) (hn : 2 ≤ n) :
    encodedCoupling n * encodedAnalysis n = 1 ∧
    encodedAnalysis n * encodedCoupling n = schurCodeProjector n := by sorry

end QAlgorithms.Papers.Independent.Renew46.P01

end
