-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P70_noiseless_spectral_procedure
-- name    : QAlgorithms.Papers.Independent.Intake100.P70.noiseless_spectral_procedure
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:53:13.139534+00:00
-- url     : https://prove2.me/theorems/603e9bf7-e635-4b09-a998-e85e54c27191
-- title:
--   Unnumbered: correctness of the noiseless-IPS spectral procedure
-- statement:
--   Let $\mathcal E$ be a CPTP endomorphism on a finite-dimensional nonzero complex Hilbert space. Take the right and left eigenvalue-one spaces, compute $P_0=\operatorname{supp}\operatorname{Fix}(\mathcal E)$, and compress the left space on both sides. There are canonical orthogonal tensor coordinates $B$ such that
--
--   $$A_B=P_0\operatorname{Fix}(\mathcal E^\dagger)P_0,\qquad\operatorname{Fix}(\mathcal E)_+\simeq_1(A_B)_+.$$
--
--   Every maximum noiseless convex density code is isometric onto $(A_B)_+$. Thus the spectral procedure returns the entire noiseless IPS shape, without assuming diagonalizability or assigning a bit runtime.
-- source:
--   Information preserving structures: A general framework for quantum zero-error information, arXiv:1006.1358v1, PDF p. 16, Unnumbered: correctness of the noiseless-IPS spectral procedure

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

/-- PDF p.16: correctness of the noiseless spectral procedure. Right/left
+1 eigenspaces are used without assuming diagonalizability. Compression and
canonical block decomposition recover the complete maximum noiseless shape.
No numerical runtime is asserted. -/
theorem noiseless_spectral_procedure {I : Type*} [Fintype I]
    [DecidableEq I] [Nonempty I] (E : Superop I I) (hE : IsChannel E) :
    ∃ B : BlockModel I, B.support = fixedSupport E ∧
      B.algebra = (fun X => fixedSupport E * X * fixedSupport E) ''
        fixedOperators (channelAdjoint E) ∧
      OneIsometric (fixedStates E) (statePart B.algebra) ∧
      ∀ C, MaximumCode (Noiseless E) C → OneIsometric C (statePart B.algebra) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P70

end
