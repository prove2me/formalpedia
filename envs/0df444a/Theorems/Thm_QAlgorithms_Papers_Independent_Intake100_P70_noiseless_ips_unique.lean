-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P70_noiseless_ips_unique
-- name    : QAlgorithms.Papers.Independent.Intake100.P70.noiseless_ips_unique
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:51:53.590996+00:00
-- url     : https://prove2.me/theorems/51845e0f-b408-4004-a1d8-306620921f6b
-- title:
--   Unnumbered: unique noiseless IPS
-- statement:
--   Let $\mathcal E$ be a CPTP endomorphism on a finite-dimensional nonzero complex Hilbert space. A 1-isometry is a complex-linear identification of the code spans that maps the normalized state sets bijectively and preserves every weighted trace-norm distance. The full fixed-state set is maximum noiseless, and every maximum noiseless convex density code has that same shape:
--
--   $$\operatorname{Fix}(\mathcal E)_+\text{ is maximum noiseless},\qquad C\simeq_1\operatorname{Fix}(\mathcal E)_+.$$
--
--   The recovery label is the identity, so this identifies one noiseless IPS rather than one physical gauge-code subset.
-- source:
--   Information preserving structures: A general framework for quantum zero-error information, arXiv:1006.1358v1, PDF p. 10, Unnumbered: unique noiseless IPS

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

/-- PDF pp.10,12,16: the unique noiseless IPS, with the identity recovery label.
Uniqueness is of the isometry class, not of the physical gauge-code subset. -/
theorem noiseless_ips_unique {I : Type*} [Fintype I]
    [DecidableEq I] [Nonempty I] (E : Superop I I) (hE : IsChannel E) :
    MaximumCode (Noiseless E) (fixedStates E) ∧
      ∀ C, MaximumCode (Noiseless E) C → OneIsometric C (fixedStates E) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P70

end
