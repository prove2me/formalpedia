-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_primeClass_eq_signal_iff__5183e8dacdc7
-- name    : P2M_Formalism_BasicNotions_primeClass_eq_signal_iff__5183e8dacdc7
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T18:30:45.514368+00:00
-- url     : https://prove2.me/theorems/4c07a380-c82c-4320-8afa-d4d4c0244826
-- title:
--   P2 M Formalism Basic Notions prime Class eq signal iff  5183e8dacdc7: P2 M Formalism Basic Notions prime Class eq signal iff  5183e8dacdc7
-- statement:
--   The P2 M Formalism Basic Notions prime Class eq signal iff  5183e8dacdc7 construction uses the P2 M Formalism Basic Notions prime Class eq signal iff  5183e8dacdc7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/HostCls.lean#L116-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/HostCls.lean#L116-L125

import Definitions.Def_Formalism_LocalRingCardinality_DataHost
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Definitions.Def_Formalism_LocalRingCardinality_HostCls
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Formalism.FrobeniusOrbits Formalism.HC
open Formalism Formalism.BasicNotions
variable {φ : Frame} (H : HostRaw φ) {p : ℕ}
variable {H}

theorem P2M_Formalism_BasicNotions_primeClass_eq_signal_iff__5183e8dacdc7 (hp : p.Prime) : primeClass H p = .signal ↔
    ¬ p ∣ H.condN ∧ jacobiSym (-(H.d : ℤ)) p = -1 ∧ H.psAt p = 1 := by sorry

alias «Formalism».«BasicNotions».«primeClass_eq_signal_iff'» := P2M_Formalism_BasicNotions_primeClass_eq_signal_iff__5183e8dacdc7
