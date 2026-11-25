-- Prove2me | Theorems.Thm_PI_BridgeMaxCptWork_mem_KGA_iff
-- name    : PI.BridgeMaxCptWork.mem_KGA_iff
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:26:27.302799+00:00
-- url     : https://prove2.me/theorems/d5dbe98d-2afe-4a1a-aad1-419a061e4b75
-- title:
--   Bridge Max Cpt Work: mem KGA iff
-- statement:
--   The Bridge Max Cpt Work construction uses the mem KGA iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MaximalCompactConjugacy/Assembly.lean#L67-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MaximalCompactConjugacy/Assembly.lean#L67-L70

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FundamentalEquivalence_AdBridge
import Definitions.Def_Formalism_PeriodIntegrals_AdBridgeSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MaximalCompactConjugacy_Assembly
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.BridgeMaxCptWork
open NumberField IsDedekindDomain Matrix
open Formalism.MainNotions.S (AutInst uMat)
open Formalism.L2.SG.AdBridge

theorem PI.BridgeMaxCptWork.mem_KGA_iff (hR : PI.AdBridgeSteps.RealK) (hF : PI.AdBridgeSteps.FinK) (I : AutInst)
    (e : I.GA ≃ₜ* HAd I) (hb : IsBridge I e) (x : I.GA) : x ∈ KGA I ↔ e x ∈ KHA I := by sorry
