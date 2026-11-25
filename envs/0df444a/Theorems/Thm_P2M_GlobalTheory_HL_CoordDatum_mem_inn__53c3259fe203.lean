-- Prove2me | Theorems.Thm_P2M_GlobalTheory_HL_CoordDatum_mem_inn__53c3259fe203
-- name    : P2M_GlobalTheory_HL_CoordDatum_mem_inn__53c3259fe203
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T00:06:06.261893+00:00
-- url     : https://prove2.me/theorems/f7fefa6d-466e-4d3f-9260-2369e80421c2
-- title:
--   P2 M Global Theory HL Coord Datum mem inn  53c3259fe203: P2 M Global Theory HL Coord Datum mem inn  53c3259fe203
-- statement:
--   The P2 M Global Theory HL Coord Datum mem inn  53c3259fe203 construction uses the P2 M Global Theory HL Coord Datum mem inn  53c3259fe203 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermitianFramePairCoordinatesTransportInnerData.lean#L87-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermitianFramePairCoordinatesTransportInnerData.lean#L87-L90

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_IsTermOver
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GgNone
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFramePairCoordinatesTransportInnerData
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.CoordDatum
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r k : ℕ}
variable {P : LocNG.FPair H r} {S : Frames M.L r k} (c : Coord P S)

theorem P2M_GlobalTheory_HL_CoordDatum_mem_inn__53c3259fe203 (f : Fin (r + 1) → V) (L : Submodule M.L.O (H.Wb f)) (x : H.perp (H.X f)) :
    c.e x ∈ c.inn f L ↔ H.mkW f x ∈ L := by sorry

alias «GlobalTheory».«HL».«CoordDatum».«mem_inn'» := P2M_GlobalTheory_HL_CoordDatum_mem_inn__53c3259fe203
