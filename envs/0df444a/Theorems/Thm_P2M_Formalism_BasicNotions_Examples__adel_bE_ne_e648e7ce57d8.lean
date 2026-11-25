-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__adel_bE_ne_e648e7ce57d8
-- name    : P2M_Formalism_BasicNotions_Examples__adel_bE_ne_e648e7ce57d8
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T13:05:50.613808+00:00
-- url     : https://prove2.me/theorems/a2cb481a-a6b9-51c4-8975-5b796b802506
-- title:
--   P2 M Formalism Basic Notions Examples  adel b E ne e648e7ce57d8: P2 M Formalism Basic Notions Examples  adel b E ne e648e7ce57d8
-- statement:
--   The P2 M Formalism Basic Notions Examples  adel b E ne e648e7ce57d8 construction uses the P2 M Formalism Basic Notions Examples  adel b E ne e648e7ce57d8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/Adelic.lean#L335-L340
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/Adelic.lean#L335-L340

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

theorem P2M_Formalism_BasicNotions_Examples__adel_bE_ne_e648e7ce57d8 : (H.sqd : H.E) ≠ 0 := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«adel_bE_ne» := P2M_Formalism_BasicNotions_Examples__adel_bE_ne_e648e7ce57d8
