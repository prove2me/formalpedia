-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__adel_aE_sq_12a969316814
-- name    : P2M_Formalism_BasicNotions_Examples__adel_aE_sq_12a969316814
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T13:08:02.892382+00:00
-- url     : https://prove2.me/theorems/db123284-4564-423e-84d6-3cd4d6f160e3
-- title:
--   P2 M Formalism Basic Notions Examples  adel a E sq 12a969316814: P2 M Formalism Basic Notions Examples  adel a E sq 12a969316814
-- statement:
--   The P2 M Formalism Basic Notions Examples  adel a E sq 12a969316814 construction uses the P2 M Formalism Basic Notions Examples  adel a E sq 12a969316814 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/Adelic.lean#L309-L309
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/Adelic.lean#L309-L309

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

theorem P2M_Formalism_BasicNotions_Examples__adel_aE_sq_12a969316814 : H.sqq ^ 2 = -(H.q : H.E) := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«adel_aE_sq» := P2M_Formalism_BasicNotions_Examples__adel_aE_sq_12a969316814
