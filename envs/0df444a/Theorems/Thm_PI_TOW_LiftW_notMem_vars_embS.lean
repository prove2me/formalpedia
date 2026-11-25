-- Prove2me | Theorems.Thm_PI_TOW_LiftW_notMem_vars_embS
-- name    : PI.TOW.LiftW.notMem_vars_embS
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:28:49.54925+00:00
-- url     : https://prove2.me/theorems/211c3905-ead7-4a8d-a44a-04bedc7704d3
-- title:
--   Lift W: not Mem vars emb S
-- statement:
--   The Lift W construction uses the not Mem vars emb S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TensorOperator/NotMemVarsEmbS.lean#L21-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TensorOperator/NotMemVarsEmbS.lean#L21-L28

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorOperator_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorOperator_NotMemVarsEmbS
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open PI PI.TOW PI.TOW.LiftW
open PI.TO PI.TOW
variable {K : Type} [CommRing K] {n' k : ℕ}

theorem PI.TOW.LiftW.notMem_vars_embS {t a : Fin n'} (h : a ≠ t) (b : Fin k) (W : MvPolynomial (Fin k) K) :
    (t, b) ∉ (embS K a W).vars := by sorry
