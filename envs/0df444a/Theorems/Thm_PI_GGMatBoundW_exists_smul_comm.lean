-- Prove2me | Theorems.Thm_PI_GGMatBoundW_exists_smul_comm
-- name    : PI.GGMatBoundW.exists_smul_comm
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:30:37.977274+00:00
-- url     : https://prove2.me/theorems/47f6eb57-3b99-5c73-88ec-41bb5a51ae91
-- title:
--   GGMat Bound W: exists smul comm
-- statement:
--   The GGMat Bound W construction uses the exists smul comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MatrixCoefficientBound/MatrixCoefficientEquation.lean#L27-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MatrixCoefficientBound/MatrixCoefficientEquation.lean#L27-L28

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

theorem PI.GGMatBoundW.exists_smul_comm (i j : X) : (∃ x : Gᵐᵒᵖ, x • j = i) ↔ ∃ x : Gᵐᵒᵖ, x • i = j := by sorry
