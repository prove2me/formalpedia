-- Prove2me | Theorems.Thm_PI_BridgeMaxCptWork_conj_unitary_iff
-- name    : PI.BridgeMaxCptWork.conj_unitary_iff
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:25:44.613558+00:00
-- url     : https://prove2.me/theorems/92b873a1-1989-4b5c-bf31-f636854afc0c
-- title:
--   Bridge Max Cpt Work: conj unitary iff
-- statement:
--   The Bridge Max Cpt Work construction uses the conj unitary iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MaximalCompactConjugacy/Assembly.lean#L13-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MaximalCompactConjugacy/Assembly.lean#L13-L35

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

theorem PI.BridgeMaxCptWork.conj_unitary_iff {n : ℕ} (P θ : Matrix (Fin n) (Fin n) ℂ) (hP : IsUnit P) :
    ((P⁻¹ * θ * P)ᴴ * (P⁻¹ * θ * P) = 1) ↔
      θᴴ * ((P⁻¹)ᴴ * P⁻¹) * θ = (P⁻¹)ᴴ * P⁻¹ := by sorry
