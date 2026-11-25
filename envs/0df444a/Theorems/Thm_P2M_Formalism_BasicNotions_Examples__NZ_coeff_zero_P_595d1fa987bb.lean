-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_coeff_zero_P_595d1fa987bb
-- name    : P2M_Formalism_BasicNotions_Examples__NZ_coeff_zero_P_595d1fa987bb
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:52:49.423669+00:00
-- url     : https://prove2.me/theorems/2deae3ca-f8d2-4ffc-8f23-d62b52a44f8f
-- title:
--   P2 M Formalism Basic Notions Examples  NZ coeff zero P 595d1fa987bb: P2 M Formalism Basic Notions Examples  NZ coeff zero P 595d1fa987bb
-- statement:
--   The P2 M Formalism Basic Notions Examples  NZ coeff zero P 595d1fa987bb construction uses the P2 M Formalism Basic Notions Examples  NZ coeff zero P 595d1fa987bb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZTypeB.lean#L238-L245
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZTypeB.lean#L238-L245

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

theorem P2M_Formalism_BasicNotions_Examples__NZ_coeff_zero_P_595d1fa987bb : P.coeff 0 ≠ 0 := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«NZ».«coeff_zero_P» := P2M_Formalism_BasicNotions_Examples__NZ_coeff_zero_P_595d1fa987bb
