-- Prove2me | Theorems.Thm_P2M_Formalism_L2_Host_ramificationIdx__eq_one_29b79749b1e0
-- name    : P2M_Formalism_L2_Host_ramificationIdx__eq_one_29b79749b1e0
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:58:09.437987+00:00
-- url     : https://prove2.me/theorems/9393b5d3-f07e-4291-ad43-b109b42ae390
-- title:
--   P2 M Formalism L2 Host ramification Idx  eq one 29b79749b1e0: P2 M Formalism L2 Host ramification Idx  eq one 29b79749b1e0
-- statement:
--   The P2 M Formalism L2 Host ramification Idx  eq one 29b79749b1e0 construction uses the P2 M Formalism L2 Host ramification Idx  eq one 29b79749b1e0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/UnitaryNorms/RamificationIdxEqOneOfNotDvd.lean#L64-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/UnitaryNorms/RamificationIdxEqOneOfNotDvd.lean#L64-L71

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataHost
import Definitions.Def_Formalism_FrobeniusOrbits_HostCorollaries
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_RamificationIdxEqOneOfNotDvd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Ideal
open Formalism Formalism.L2 Formalism.L2.Host
open Formalism.BasicNotions Formalism.FrobeniusOrbits
variable {R : Ranks} (H : Formalism.BasicNotions.Host R)

theorem P2M_Formalism_L2_Host_ramificationIdx__eq_one_29b79749b1e0 (p : ℕ) [Fact p.Prime] (hnd : ¬ p ∣ H.condN)
    (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})] :
    (span {(p : ℤ)}).ramificationIdx' P = 1 := by sorry

alias «Formalism».«L2».«Host».«ramificationIdx'_eq_one» := P2M_Formalism_L2_Host_ramificationIdx__eq_one_29b79749b1e0
