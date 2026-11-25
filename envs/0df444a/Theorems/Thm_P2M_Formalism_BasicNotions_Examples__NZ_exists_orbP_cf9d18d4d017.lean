-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_exists_orbP_cf9d18d4d017
-- name    : P2M_Formalism_BasicNotions_Examples__NZ_exists_orbP_cf9d18d4d017
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:54:00.048707+00:00
-- url     : https://prove2.me/theorems/58b0611b-81cb-41e7-93cf-93afad425a0d
-- title:
--   P2 M Formalism Basic Notions Examples  NZ exists orb P cf9d18d4d017: P2 M Formalism Basic Notions Examples  NZ exists orb P cf9d18d4d017
-- statement:
--   The P2 M Formalism Basic Notions Examples  NZ exists orb P cf9d18d4d017 construction uses the P2 M Formalism Basic Notions Examples  NZ exists orb P cf9d18d4d017 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZTypeB.lean#L112-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZTypeB.lean#L112-L142

import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZTypeA
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZTypeB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.NZ
open Polynomial Formalism.CyclotomicNorms Formalism.CyclotomicNorms.CycleTypeFiniteOrder
variable {g : ℕ} [hg : Fact g.Prime]
variable {d : ℕ} (hd : 1 ≤ d) (u : (Fbar g)ˣ) (hu : orderOf u = g ^ d - 1)
include hd hu

theorem P2M_Formalism_BasicNotions_Examples__NZ_exists_orbP_cf9d18d4d017 : ∃ P : (ZMod g)[X], P.map (algebraMap (ZMod g) (Fbar g)) = orbQ d u ∧
    P.natDegree = d ∧ P.Monic := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«NZ».«exists_orbP» := P2M_Formalism_BasicNotions_Examples__NZ_exists_orbP_cf9d18d4d017
