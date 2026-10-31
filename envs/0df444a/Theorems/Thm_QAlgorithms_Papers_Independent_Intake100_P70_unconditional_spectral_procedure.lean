-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P70_unconditional_spectral_procedure
-- name    : QAlgorithms.Papers.Independent.Intake100.P70.unconditional_spectral_procedure
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:54:33.757903+00:00
-- url     : https://prove2.me/theorems/6ecea112-1b17-464f-be2e-baf11c4471cb
-- title:
--   Unnumbered: correctness of the unconditional-IPS spectral procedure
-- statement:
--   Let $\mathcal E$ be CPTP between finite-dimensional nonzero complex spaces, and construct the full-input transpose recovery $\widehat{\mathcal E}$ with support inverses and a maximally mixed kernel completion. Then
--
--   $$\widehat{\mathcal E}\text{ is CPTP},\qquad\widehat{\mathcal E}(\mathcal E(I))=I,\qquad A=\operatorname{Fix}(\widehat{\mathcal E}\circ\mathcal E)$$
--
--   is a unital matrix star algebra whose normalized states represent the unique unconditional IPS: every unconditional code embeds isometrically and every maximum one has its full shape. Singular $\mathcal E(I)$ is allowed. This is mathematical correctness of extracting the +1 eigenspace, without a runtime claim.
-- source:
--   Information preserving structures: A general framework for quantum zero-error information, arXiv:1006.1358v1, PDF p. 17, Unnumbered: correctness of the unconditional-IPS spectral procedure

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P70

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open Filter

namespace QAlgorithms.Papers.Independent.Intake100.P70

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P21 (channelAdjoint)

open QAlgorithms.Papers.Independent.Information100.P07 (positivePart negativePart)

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P34 (supportProjector)

/-- PDF p.17: correctness of the unconditional procedure, using the +1
fixed space of the computed transpose composite. Singular E(I) is allowed;
the explicitly completed recovery is global CPTP and the composite is unital. -/
theorem unconditional_spectral_procedure {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] [Nonempty I] [Nonempty J]
    (E : Superop I J) (hE : IsChannel E) :
    IsChannel (fullTransposeRecovery E) ∧ fullTransposeRecovery E (E 1) = 1 ∧
      UnconditionalStructure E (fixedOperators (fullTransposeRecovery E ∘ E)) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P70

end
