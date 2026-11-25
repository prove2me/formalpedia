-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Host_four_le_n__da3ddea1485c
-- name    : P2M_Formalism_BasicNotions_Host_four_le_n__da3ddea1485c
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:53:07.796525+00:00
-- url     : https://prove2.me/theorems/649d305a-bdab-45c9-bf93-dffc3436d514
-- title:
--   P2 M Formalism Basic Notions Host four le n  da3ddea1485c: P2 M Formalism Basic Notions Host four le n  da3ddea1485c
-- statement:
--   The P2 M Formalism Basic Notions Host four le n  da3ddea1485c construction uses the P2 M Formalism Basic Notions Host four le n  da3ddea1485c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/HostCls.lean#L176-L176
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/HostCls.lean#L176-L176

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
open Formalism.BasicNotions.Host
variable {R : Ranks} (H : Host R)
include H

theorem P2M_Formalism_BasicNotions_Host_four_le_n__da3ddea1485c : 4 ≤ R.n := by sorry

alias «Formalism».«BasicNotions».«Host».«four_le_n'» := P2M_Formalism_BasicNotions_Host_four_le_n__da3ddea1485c
