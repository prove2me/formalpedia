-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__adel_alg_6c628a2428b5
-- name    : P2M_Formalism_BasicNotions_Examples__adel_alg_6c628a2428b5
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:53:37.734101+00:00
-- url     : https://prove2.me/theorems/eac242e3-7da1-4024-a6fc-1b3508ed94e2
-- title:
--   P2 M Formalism Basic Notions Examples  adel alg 6c628a2428b5: P2 M Formalism Basic Notions Examples  adel alg 6c628a2428b5
-- statement:
--   The P2 M Formalism Basic Notions Examples  adel alg 6c628a2428b5 construction uses the P2 M Formalism Basic Notions Examples  adel alg 6c628a2428b5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/Adelic.lean#L533-L537
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/Adelic.lean#L533-L537

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

theorem P2M_Formalism_BasicNotions_Examples__adel_alg_6c628a2428b5 {B : Type*} [CommRing B] (τ : B →+* B) (s t u : B) (N : ℤ)
    (hs : τ s = s) (ht : τ t = t) (hτu : τ u = 1 - u) (hu : u * (1 - u) = N)
    (hk : s * s + s * t + (N : B) * (t * t) = -1) : τ (s + u * t) * (s + u * t) = -1 := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«adel_alg» := P2M_Formalism_BasicNotions_Examples__adel_alg_6c628a2428b5
