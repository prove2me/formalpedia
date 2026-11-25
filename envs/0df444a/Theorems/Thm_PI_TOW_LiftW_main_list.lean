-- Prove2me | Theorems.Thm_PI_TOW_LiftW_main_list
-- name    : PI.TOW.LiftW.main_list
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:28:55.167436+00:00
-- url     : https://prove2.me/theorems/1dcc9176-e0f1-48b8-bacd-0a6ca7b4575d
-- title:
--   Lift W: main list
-- statement:
--   The Lift W construction uses the main list property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TensorOperator/NotMemVarsEmbS.lean#L61-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TensorOperator/NotMemVarsEmbS.lean#L61-L79

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

theorem PI.TOW.LiftW.main_list (w : Fin n' → List (Fin k × Fin k)) (G : Fin n' → MvPolynomial (Fin k) K)
    (ts : List (Fin n')) (hts : ts.Nodup) :
    opWord (ts.flatMap fun t => liftW t (w t)) (∏ s, embS K s (G s)) =
      ∏ s, embS K s (if s ∈ ts then word1 (w s) (G s) else G s) := by sorry
