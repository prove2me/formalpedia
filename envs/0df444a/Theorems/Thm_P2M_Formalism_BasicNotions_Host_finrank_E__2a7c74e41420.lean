-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Host_finrank_E__2a7c74e41420
-- name    : P2M_Formalism_BasicNotions_Host_finrank_E__2a7c74e41420
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:53:29.422744+00:00
-- url     : https://prove2.me/theorems/d2d6fb22-4459-4a28-8a4a-a1dcbf1e9a76
-- title:
--   P2 M Formalism Basic Notions Host finrank E  2a7c74e41420: P2 M Formalism Basic Notions Host finrank E  2a7c74e41420
-- statement:
--   The P2 M Formalism Basic Notions Host finrank E  2a7c74e41420 construction uses the P2 M Formalism Basic Notions Host finrank E  2a7c74e41420 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/HostCls.lean#L245-L248
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/HostCls.lean#L245-L248

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

theorem P2M_Formalism_BasicNotions_Host_finrank_E__2a7c74e41420 : Module.finrank ℚ H.E = 2 * R.f := by sorry

alias «Formalism».«BasicNotions».«Host».«finrank_E'» := P2M_Formalism_BasicNotions_Host_finrank_E__2a7c74e41420
