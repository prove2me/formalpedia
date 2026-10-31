-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P70_corollary3_maximum_noiseless_shape
-- name    : QAlgorithms.Papers.Independent.Intake100.P70.corollary3_maximum_noiseless_shape
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:34:36.193997+00:00
-- url     : https://prove2.me/theorems/81baf7a0-5fbb-4a84-b139-8f317229d06a
-- title:
--   Corollary 3: maximum noiseless codes have the entire fixed-state shape
-- statement:
--   Let $\mathcal E$ be a CPTP endomorphism on a finite-dimensional nonzero complex Hilbert space. Maximum means that no code satisfying the same criterion has a proper subset 1-isometric to $C$. A 1-isometry is a complex-linear identification of the code spans that maps the normalized state sets bijectively and preserves every weighted trace-norm distance. Every maximum convex noiseless density code satisfies
--
--   $$C\simeq_1\{\rho\ge0:\operatorname{Tr}\rho=1,\ \mathcal E(\rho)=\rho\}.$$
--
--   The full state set, rather than the unbounded fixed-operator space, determines the noiseless shape.
-- source:
--   Information preserving structures: A general framework for quantum zero-error information, arXiv:1006.1358v1, PDF p. 8, Corollary 3: maximum noiseless codes have the entire fixed-state shape

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

/-- PDF pp.8,22, Corollary 3. Full fixed-point set means fixed density matrices. -/
theorem corollary3_maximum_noiseless_shape {I : Type*} [Fintype I]
    [DecidableEq I] [Nonempty I] (E : Superop I I) (hE : IsChannel E)
    (C : Set (Op I)) (hC : MaximumCode (Noiseless E) C) :
    OneIsometric C (fixedStates E) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P70

end
