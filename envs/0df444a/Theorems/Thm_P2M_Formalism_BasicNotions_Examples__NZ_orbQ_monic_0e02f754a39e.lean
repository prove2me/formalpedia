-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_orbQ_monic_0e02f754a39e
-- name    : P2M_Formalism_BasicNotions_Examples__NZ_orbQ_monic_0e02f754a39e
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:46:27.509809+00:00
-- url     : https://prove2.me/theorems/e5c3f24a-218d-4cca-86e3-ea6bac5f0f2f
-- title:
--   P2 M Formalism Basic Notions Examples  NZ orb Q monic 0e02f754a39e: P2 M Formalism Basic Notions Examples  NZ orb Q monic 0e02f754a39e
-- statement:
--   The P2 M Formalism Basic Notions Examples  NZ orb Q monic 0e02f754a39e construction uses the P2 M Formalism Basic Notions Examples  NZ orb Q monic 0e02f754a39e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZTypeB.lean#L90-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZTypeB.lean#L90-L90

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

theorem P2M_Formalism_BasicNotions_Examples__NZ_orbQ_monic_0e02f754a39e : (orbQ d u).Monic := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«NZ».«orbQ_monic» := P2M_Formalism_BasicNotions_Examples__NZ_orbQ_monic_0e02f754a39e
