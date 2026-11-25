-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_irreducible_P_8763ba5db034
-- name    : P2M_Formalism_BasicNotions_Examples__NZ_irreducible_P_8763ba5db034
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:53:02.072814+00:00
-- url     : https://prove2.me/theorems/58f79bff-1c36-432c-b85d-e64c1822707d
-- title:
--   P2 M Formalism Basic Notions Examples  NZ irreducible P 8763ba5db034: P2 M Formalism Basic Notions Examples  NZ irreducible P 8763ba5db034
-- statement:
--   The P2 M Formalism Basic Notions Examples  NZ irreducible P 8763ba5db034 construction uses the P2 M Formalism Basic Notions Examples  NZ irreducible P 8763ba5db034 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZTypeB.lean#L215-L235
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZTypeB.lean#L215-L235

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

theorem P2M_Formalism_BasicNotions_Examples__NZ_irreducible_P_8763ba5db034 (hPd : P.natDegree = d) : Irreducible P := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«NZ».«irreducible_P» := P2M_Formalism_BasicNotions_Examples__NZ_irreducible_P_8763ba5db034
