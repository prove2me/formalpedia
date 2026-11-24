-- Prove2me | Theorems.Thm_PI_BlockRatReal_UnitaryGroupMassFormula_eval_map_rowAct
-- name    : PI.BlockRatReal.UnitaryGroupMassFormula.eval_map_rowAct
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:43:20.620539+00:00
-- url     : https://prove2.me/theorems/1db40a20-3edf-4886-8241-0ed678c07ead
-- title:
--   Unitary Group Mass Formula: eval map row Act
-- statement:
--   The Unitary Group Mass Formula construction uses the eval map row Act property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RationalRealBlocks/Bridge.lean#L28-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RationalRealBlocks/Bridge.lean#L28-L38

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_BlockRatReal
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_WeylLeDual
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_SumIcoTsubTelescope
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_RowDivStable
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_DualWeylMap
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_DualWeylRowStable
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RationalRealBlocks_Bridge
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Matrix
noncomputable section
open PI PI.BlockRatReal PI.BlockRatReal.UnitaryGroupMassFormula

theorem PI.BlockRatReal.UnitaryGroupMassFormula.eval_map_rowAct {LL : Type} [Field LL] (φ : LL →+* ℂ) {k : ℕ} (g : Matrix (Fin k) (Fin k) LL)
    (F : MvPolynomial (Fin k × Fin k) LL) (z : Matrix (Fin k) (Fin k) ℂ) :
    eval (fun x => z x.1 x.2) (MvPolynomial.map φ (Formalism.GradedWeylDivisibility.rowAct LL g F)) =
      eval (fun x => (g.map φ * z) x.1 x.2) (MvPolynomial.map φ F) := by sorry
