-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__adel_hom_key_afaa1b4817b3
-- name    : P2M_Formalism_BasicNotions_Examples__adel_hom_key_afaa1b4817b3
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:54:06.403987+00:00
-- url     : https://prove2.me/theorems/76d20687-301a-4fc8-a3e8-9c7dc975f685
-- title:
--   P2 M Formalism Basic Notions Examples  adel hom key afaa1b4817b3: P2 M Formalism Basic Notions Examples  adel hom key afaa1b4817b3
-- statement:
--   The P2 M Formalism Basic Notions Examples  adel hom key afaa1b4817b3 construction uses the P2 M Formalism Basic Notions Examples  adel hom key afaa1b4817b3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/Adelic.lean#L527-L531
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/Adelic.lean#L527-L531

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

theorem P2M_Formalism_BasicNotions_Examples__adel_hom_key_afaa1b4817b3 {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (S T : A) (N : ℤ)
    (h : S * S + S * T + (N : A) * (T * T) = -1) :
    f S * f S + f S * f T + (N : B) * (f T * f T) = -1 := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«adel_hom_key» := P2M_Formalism_BasicNotions_Examples__adel_hom_key_afaa1b4817b3
