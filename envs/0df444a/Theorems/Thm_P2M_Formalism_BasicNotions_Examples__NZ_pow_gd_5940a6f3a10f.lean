-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_pow_gd_5940a6f3a10f
-- name    : P2M_Formalism_BasicNotions_Examples__NZ_pow_gd_5940a6f3a10f
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:02:17.825273+00:00
-- url     : https://prove2.me/theorems/70fc7908-2a82-4797-9252-630cc81ab309
-- title:
--   P2 M Formalism Basic Notions Examples  NZ pow gd 5940a6f3a10f: P2 M Formalism Basic Notions Examples  NZ pow gd 5940a6f3a10f
-- statement:
--   The P2 M Formalism Basic Notions Examples  NZ pow gd 5940a6f3a10f construction uses the P2 M Formalism Basic Notions Examples  NZ pow gd 5940a6f3a10f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZTypeB.lean#L43-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZTypeB.lean#L43-L45

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

theorem P2M_Formalism_BasicNotions_Examples__NZ_pow_gd_5940a6f3a10f : u ^ (g ^ d) = u := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«NZ».«pow_gd» := P2M_Formalism_BasicNotions_Examples__NZ_pow_gd_5940a6f3a10f
