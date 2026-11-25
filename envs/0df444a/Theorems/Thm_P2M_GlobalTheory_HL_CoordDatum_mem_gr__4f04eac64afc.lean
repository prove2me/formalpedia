-- Prove2me | Theorems.Thm_P2M_GlobalTheory_HL_CoordDatum_mem_gr__4f04eac64afc
-- name    : P2M_GlobalTheory_HL_CoordDatum_mem_gr__4f04eac64afc
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T00:06:51.124351+00:00
-- url     : https://prove2.me/theorems/93e4bb23-4c31-489d-abc1-536db072236f
-- title:
--   P2 M Global Theory HL Coord Datum mem gr  4f04eac64afc: P2 M Global Theory HL Coord Datum mem gr  4f04eac64afc
-- statement:
--   The P2 M Global Theory HL Coord Datum mem gr  4f04eac64afc construction uses the P2 M Global Theory HL Coord Datum mem gr  4f04eac64afc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermitianFramePairCoordinatesTransportInnerData.lean#L149-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermitianFramePairCoordinatesTransportInnerData.lean#L149-L152

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

theorem P2M_GlobalTheory_HL_CoordDatum_mem_gr__4f04eac64afc (d : LocNG.Datum P) (x' : ↥(H.perp (H.X P.B.f))) (x : ↥(H.perp (H.X P.A.f))) :
    (c.e x', c.e x) ∈ (c.dat d).2.2 ↔ Q d x' x := by sorry

alias «GlobalTheory».«HL».«CoordDatum».«mem_gr'» := P2M_GlobalTheory_HL_CoordDatum_mem_gr__4f04eac64afc
