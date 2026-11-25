-- Prove2me | Theorems.Thm_PI_SymDistWork_inUJ_coe
-- name    : PI.SymDistWork.inUJ_coe
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T08:29:01.616608+00:00
-- url     : https://prove2.me/theorems/d63e1a21-ea45-47a8-b372-1a07bec12b53
-- title:
--   Sym Dist Work: in UJ coe
-- statement:
--   The Sym Dist Work construction uses the in UJ coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SymmetricDistance/SymDistOf.lean#L51-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SymmetricDistance/SymDistOf.lean#L51-L53

import Definitions.Def_Formalism_PeriodIntegrals_SymDist
import Definitions.Def_Formalism_PeriodIntegrals_ExpTri
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_IndefiniteUnitaryPreservesForm
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexificationHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SymmetricDistance_SymDistOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PI PI.SymDistWork
open Formalism.REAL
variable {n : ℕ}

theorem PI.SymDistWork.inUJ_coe {ε : Fin n → Bool} (g : UJ ε) :
    inUJ ε ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) := by sorry
