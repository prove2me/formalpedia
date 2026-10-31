-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P70_initialization_free_iff
-- name    : QAlgorithms.Papers.Independent.Intake100.P70.initialization_free_iff
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:55:22.562815+00:00
-- url     : https://prove2.me/theorems/8bef8a03-a00f-4f3c-8c0d-cd5a39a04a66
-- title:
--   Unnumbered: initialization-free NS iff noiseless and unconditional
-- statement:
--   Let $\mathcal E$ be a CPTP endomorphism on a finite-dimensional nonzero complex Hilbert space. Fix a nonzero embedded sector $A\otimes B$ with isometry $V:A\otimes B\to H$, support $P=VV^\dagger$, and subnormalized logical marginal $L(X)=\operatorname{Tr}_B(V^\dagger XV)$. Then
--
--   $$[\ \forall\rho\text{ density on }H,\ L(\mathcal E(\rho))=L(\rho)\ ]\iff[\ A\text{ is a strict noiseless subsystem and is unconditionally preserved}\ ].$$
--
--   Strict noiselessness includes confinement and identity action on the logical factor for supported states. Unconditional preservation here simulates every logical projective partition, together with the outside-sector outcome, on all physical inputs. Outside populations and coherences are unrestricted.
-- source:
--   Information preserving structures: A general framework for quantum zero-error information, arXiv:1006.1358v1, PDF p. 17, Unnumbered: initialization-free NS iff noiseless and unconditional

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

/-- PDF pp.17–18: strict Eq.(5) initialization-free NS iff noiseless and
unconditionally preserved. All gauges and arbitrary physical density inputs
are included, including sector population and off-diagonal input blocks. -/
theorem initialization_free_iff {I : Type*} [Fintype I]
    [DecidableEq I] [Nonempty I] (E : Superop I I) (hE : IsChannel E)
    (S : Subsystem I) :
    InitializationFree E S ↔
      StrictNoiselessSubsystem E S ∧ UnconditionalSubsystem E S := by sorry

end QAlgorithms.Papers.Independent.Intake100.P70

end
