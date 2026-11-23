-- Prove2me | Theorems.Thm_PI_GGMatBoundW_eq_of_smul_eq_of_free
-- name    : PI.GGMatBoundW.eq_of_smul_eq_of_free
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:28:49.62623+00:00
-- url     : https://prove2.me/theorems/9fcf6a81-0018-40df-a05a-e1a2fb30020a
-- title:
--   GGMat Bound W: eq of smul eq of free
-- statement:
--   The GGMat Bound W construction uses the eq of smul eq of free property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MatrixCoefficientBound/MatrixCoefficientEquation.lean#L22-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MatrixCoefficientBound/MatrixCoefficientEquation.lean#L22-L25

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GGMirabolic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MatrixCoefficientBound_PermRepApply
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MatrixCoefficientBound_GammaMatrixInverse
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MatrixCoefficientBound_MatrixCoefficientEquation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Matrix
open scoped ComplexConjugate
noncomputable section
open Classical
open PI PI.GGMatBoundW
open Formalism.L2.SG.GGMirabolic
variable {G : Type} [Group G] {X : Type} [MulAction Gᵐᵒᵖ X]

theorem PI.GGMatBoundW.eq_of_smul_eq_of_free (hfree : ∀ (x : Gᵐᵒᵖ) (j : X), x • j = j → x = 1) {a b : Gᵐᵒᵖ} {j : X}
    (h : a • j = b • j) : a = b := by sorry
