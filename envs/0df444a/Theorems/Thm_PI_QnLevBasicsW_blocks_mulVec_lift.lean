-- Prove2me | Theorems.Thm_PI_QnLevBasicsW_blocks_mulVec_lift
-- name    : PI.QnLevBasicsW.blocks_mulVec_lift
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T14:08:45.923626+00:00
-- url     : https://prove2.me/theorems/aaa9d29c-f9cc-4ee8-b1ce-797bba1fa025
-- title:
--   Qn Lev Basics W: blocks mul Vec lift
-- statement:
--   The Qn Lev Basics W construction uses the blocks mul Vec lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelLiftBasics/SplitInvInjective.lean#L120-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelLiftBasics/SplitInvInjective.lean#L120-L129

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

theorem PI.QnLevBasicsW.blocks_mulVec_lift (A : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ)
    (J : Matrix (Fin (2 * i)) (Fin (2 * i)) ℂ) (v : Fin (2 * r' + k + 1) → ℂ) :
    (fromBlocks A 0 0 J).submatrix (split k i r') (split k i r') *ᵥ liftVec k i r' v =
      liftVec k i r' (A *ᵥ v) := by sorry
