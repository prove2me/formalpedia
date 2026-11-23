-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_le_natDegree_of_dvd_81216a4a9b35
-- name    : P2M_Formalism_BasicNotions_Examples__NZ_le_natDegree_of_dvd_81216a4a9b35
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:01:53.30619+00:00
-- url     : https://prove2.me/theorems/e598be5c-2a9a-4928-8da0-c0c8da295e99
-- title:
--   P2 M Formalism Basic Notions Examples  NZ le nat Degree of dvd 81216a4a9b35: P2 M Formalism Basic Notions Examples  NZ le nat Degree of dvd 81216a4a9b35
-- statement:
--   The P2 M Formalism Basic Notions Examples  NZ le nat Degree of dvd 81216a4a9b35 construction uses the P2 M Formalism Basic Notions Examples  NZ le nat Degree of dvd 81216a4a9b35 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZTypeB.lean#L159-L212
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZTypeB.lean#L159-L212

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
variable {P : (ZMod g)[X]} (hP : P.map (algebraMap (ZMod g) (Fbar g)) = orbQ d u)
include hd hu hP

theorem P2M_Formalism_BasicNotions_Examples__NZ_le_natDegree_of_dvd_81216a4a9b35 {q : (ZMod g)[X]} (hq : q ∣ P) (hq0 : q.natDegree ≠ 0) : d ≤ q.natDegree := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«NZ».«le_natDegree_of_dvd» := P2M_Formalism_BasicNotions_Examples__NZ_le_natDegree_of_dvd_81216a4a9b35
