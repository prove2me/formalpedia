-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_mem_rootsBar_P_9cb9ba47d11d
-- name    : P2M_Formalism_BasicNotions_Examples__NZ_mem_rootsBar_P_9cb9ba47d11d
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T01:50:28.92672+00:00
-- url     : https://prove2.me/theorems/85ecefbf-aab9-4933-b120-f085e05b8981
-- title:
--   P2 M Formalism Basic Notions Examples  NZ mem roots Bar P 9cb9ba47d11d: P2 M Formalism Basic Notions Examples  NZ mem roots Bar P 9cb9ba47d11d
-- statement:
--   The P2 M Formalism Basic Notions Examples  NZ mem roots Bar P 9cb9ba47d11d construction uses the P2 M Formalism Basic Notions Examples  NZ mem roots Bar P 9cb9ba47d11d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZTypeB.lean#L153-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZTypeB.lean#L153-L155

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
include hP

theorem P2M_Formalism_BasicNotions_Examples__NZ_mem_rootsBar_P_9cb9ba47d11d {y : Fbar g} : y ∈ rootsBar P ↔ ∃ i < d, y = (u : Fbar g) ^ (g ^ i) := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«NZ».«mem_rootsBar_P» := P2M_Formalism_BasicNotions_Examples__NZ_mem_rootsBar_P_9cb9ba47d11d
