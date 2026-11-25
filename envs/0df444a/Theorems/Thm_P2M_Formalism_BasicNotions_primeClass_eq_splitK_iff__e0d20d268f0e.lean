-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_primeClass_eq_splitK_iff__e0d20d268f0e
-- name    : P2M_Formalism_BasicNotions_primeClass_eq_splitK_iff__e0d20d268f0e
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:53:38.57383+00:00
-- url     : https://prove2.me/theorems/f8dfdf8e-91f2-4bc8-b91b-80360602de91
-- title:
--   P2 M Formalism Basic Notions prime Class eq split K iff  e0d20d268f0e: P2 M Formalism Basic Notions prime Class eq split K iff  e0d20d268f0e
-- statement:
--   The P2 M Formalism Basic Notions prime Class eq split K iff  e0d20d268f0e construction uses the P2 M Formalism Basic Notions prime Class eq split K iff  e0d20d268f0e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/HostCls.lean#L111-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/HostCls.lean#L111-L114

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

theorem P2M_Formalism_BasicNotions_primeClass_eq_splitK_iff__e0d20d268f0e (hp : p.Prime) : primeClass H p = .splitK ↔
    ¬ p ∣ H.condN ∧ jacobiSym (-(H.d : ℤ)) p = 1 := by sorry

alias «Formalism».«BasicNotions».«primeClass_eq_splitK_iff'» := P2M_Formalism_BasicNotions_primeClass_eq_splitK_iff__e0d20d268f0e
