-- Prove2me | Theorems.Thm_P2M_PI_QnLevBasicsW__Lev_eq_c687ca9a93c5
-- name    : P2M_PI_QnLevBasicsW__Lev_eq_c687ca9a93c5
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T14:08:04.399704+00:00
-- url     : https://prove2.me/theorems/c512a398-9e52-447b-8cbd-cc4f22a97e03
-- title:
--   P2 M PI Qn Lev Basics W  Lev eq c687ca9a93c5: P2 M PI Qn Lev Basics W  Lev eq c687ca9a93c5
-- statement:
--   The P2 M PI Qn Lev Basics W  Lev eq c687ca9a93c5 construction uses the P2 M PI Qn Lev Basics W  Lev eq c687ca9a93c5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelLiftBasics/SplitInvInjective.lean#L66-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelLiftBasics/SplitInvInjective.lean#L66-L100

import Definitions.Def_Formalism_FormalDegreeBessel_StatementRP
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelLiftBasics_SplitInvInjective
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
open PI PI.QnLevBasicsW
open Formalism.QuantumDeterminants
variable {k i r' : ℕ}

theorem P2M_PI_QnLevBasicsW__Lev_eq_c687ca9a93c5 (g : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ) :
    ιLev k i r' g = (fromBlocks g 0 0 1).submatrix (split k i r') (split k i r') := by sorry

alias «PI».«QnLevBasicsW».«ιLev_eq» := P2M_PI_QnLevBasicsW__Lev_eq_c687ca9a93c5
