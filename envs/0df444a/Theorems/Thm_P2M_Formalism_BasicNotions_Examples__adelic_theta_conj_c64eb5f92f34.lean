-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__adelic_theta_conj_c64eb5f92f34
-- name    : P2M_Formalism_BasicNotions_Examples__adelic_theta_conj_c64eb5f92f34
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:54:09.702898+00:00
-- url     : https://prove2.me/theorems/e35a66cf-015a-472f-b298-df55c9f0b4d5
-- title:
--   P2 M Formalism Basic Notions Examples  adelic theta conj c64eb5f92f34: P2 M Formalism Basic Notions Examples  adelic theta conj c64eb5f92f34
-- statement:
--   The P2 M Formalism Basic Notions Examples  adelic theta conj c64eb5f92f34 construction uses the P2 M Formalism Basic Notions Examples  adelic theta conj c64eb5f92f34 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/Adelic.lean#L366-L370
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/Adelic.lean#L366-L370

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_UnimodUnramUnique
import Definitions.Def_Formalism_LocalRingCardinality_DataHost
import Definitions.Def_Formalism_FrobeniusOrbits_HostCorollaries
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_Adelic
import Theorems.Thm_Formalism_FrobeniusOrbits_Final_conj

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

theorem P2M_Formalism_BasicNotions_Examples__adelic_theta_conj_c64eb5f92f34 : H.conj (adelTheta H) = 1 - adelTheta H := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«adelic_theta_conj» := P2M_Formalism_BasicNotions_Examples__adelic_theta_conj_c64eb5f92f34
