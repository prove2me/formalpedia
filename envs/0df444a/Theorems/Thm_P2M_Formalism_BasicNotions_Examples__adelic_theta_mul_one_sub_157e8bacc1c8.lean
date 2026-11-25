-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__adelic_theta_mul_one_sub_157e8bacc1c8
-- name    : P2M_Formalism_BasicNotions_Examples__adelic_theta_mul_one_sub_157e8bacc1c8
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:53:25.769152+00:00
-- url     : https://prove2.me/theorems/634cece0-061d-4491-99fe-ff92b7eaa685
-- title:
--   P2 M Formalism Basic Notions Examples  adelic theta mul one sub 157e8bacc1c8: P2 M Formalism Basic Notions Examples  adelic theta mul one sub 157e8bacc1c8
-- statement:
--   The P2 M Formalism Basic Notions Examples  adelic theta mul one sub 157e8bacc1c8 construction uses the P2 M Formalism Basic Notions Examples  adelic theta mul one sub 157e8bacc1c8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/Adelic.lean#L372-L377
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/Adelic.lean#L372-L377

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

theorem P2M_Formalism_BasicNotions_Examples__adelic_theta_mul_one_sub_157e8bacc1c8 : adelTheta H * (1 - adelTheta H) = ((adelNd H : ℤ) : H.E) := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«adelic_theta_mul_one_sub» := P2M_Formalism_BasicNotions_Examples__adelic_theta_mul_one_sub_157e8bacc1c8
