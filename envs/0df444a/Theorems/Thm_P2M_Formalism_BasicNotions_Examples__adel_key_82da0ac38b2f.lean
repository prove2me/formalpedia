-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__adel_key_82da0ac38b2f
-- name    : P2M_Formalism_BasicNotions_Examples__adel_key_82da0ac38b2f
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:53:40.229196+00:00
-- url     : https://prove2.me/theorems/9f3c85d2-3e55-41c6-b032-764923e9167d
-- title:
--   P2 M Formalism Basic Notions Examples  adel key 82da0ac38b2f: P2 M Formalism Basic Notions Examples  adel key 82da0ac38b2f
-- statement:
--   The P2 M Formalism Basic Notions Examples  adel key 82da0ac38b2f construction uses the P2 M Formalism Basic Notions Examples  adel key 82da0ac38b2f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/Adelic.lean#L517-L525
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/Adelic.lean#L517-L525

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

theorem P2M_Formalism_BasicNotions_Examples__adel_key_82da0ac38b2f : adelS H * adelS H + adelS H * adelT H +
    ((adelNd H : ℤ) : FiniteAdeleRing (𝓞 H.F) H.F) * (adelT H * adelT H) = -1 := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«adel_key» := P2M_Formalism_BasicNotions_Examples__adel_key_82da0ac38b2f
