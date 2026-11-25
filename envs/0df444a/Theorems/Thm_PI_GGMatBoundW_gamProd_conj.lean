-- Prove2me | Theorems.Thm_PI_GGMatBoundW_gamProd_conj
-- name    : PI.GGMatBoundW.gamProd_conj
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:30:28.171068+00:00
-- url     : https://prove2.me/theorems/8880eaea-9cdb-5c34-91b1-6abda7a38b0e
-- title:
--   GGMat Bound W: gam Prod conj
-- statement:
--   The GGMat Bound W construction uses the gam Prod conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MatrixCoefficientBound/JointEigenvectorExists.lean#L16-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MatrixCoefficientBound/JointEigenvectorExists.lean#L16-L20

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GGMirabolic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ScalarConvolutionTrace_Reindex
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MatrixCoefficientBound_PermRepApply
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MatrixCoefficientBound_JointEigenvectorExists
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical
open PI PI.GGMatBoundW
open Formalism.L2.SG.GGMirabolic
variable {ι : Type} [Fintype ι] {Fq : ι → Type} [∀ v, Field (Fq v)] [∀ v, Fintype (Fq v)] {k : ℕ}

theorem PI.GGMatBoundW.gamProd_conj (ψ : ∀ v, AddChar (Fq v) ℂ) (g x : ∀ v, GL (Fin k) (Fq v)) :
    gamProd ψ (g * x * g⁻¹) = gamProd ψ x := by sorry
