-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__adel_bE_sq_12848b487386
-- name    : P2M_Formalism_BasicNotions_Examples__adel_bE_sq_12848b487386
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T13:08:23.513802+00:00
-- url     : https://prove2.me/theorems/d0eaf308-67d7-4ffc-861d-2836288c5556
-- title:
--   P2 M Formalism Basic Notions Examples  adel b E sq 12848b487386: P2 M Formalism Basic Notions Examples  adel b E sq 12848b487386
-- statement:
--   The P2 M Formalism Basic Notions Examples  adel b E sq 12848b487386 construction uses the P2 M Formalism Basic Notions Examples  adel b E sq 12848b487386 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/Adelic.lean#L311-L311
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/Adelic.lean#L311-L311

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_UnimodUnramUnique
import Definitions.Def_Formalism_LocalRingCardinality_DataHost
import Definitions.Def_Formalism_FrobeniusOrbits_HostCorollaries
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_Adelic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsDedekindDomain HeightOneSpectrum IsLocalRing WithZero NumberField Filter Topology
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂
open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
open scoped TensorProduct
variable {R : Formalism.BasicNotions.Ranks} (H : Formalism.BasicNotions.Host R)

theorem P2M_Formalism_BasicNotions_Examples__adel_bE_sq_12848b487386 : H.sqd ^ 2 = -(H.d : H.E) := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«adel_bE_sq» := P2M_Formalism_BasicNotions_Examples__adel_bE_sq_12848b487386
