-- Prove2me | Theorems.Thm_P2M_GlobalTheory_EisBL_NilAlg_blk_map__4db2ce721b87
-- name    : P2M_GlobalTheory_EisBL_NilAlg_blk_map__4db2ce721b87
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T13:10:59.190345+00:00
-- url     : https://prove2.me/theorems/49cc249f-cc56-42a2-a104-63522aeb0217
-- title:
--   P2 M Global Theory Eis BL Nil Alg blk map  4db2ce721b87: P2 M Global Theory Eis BL Nil Alg blk map  4db2ce721b87
-- statement:
--   The P2 M Global Theory Eis BL Nil Alg blk map  4db2ce721b87 construction uses the P2 M Global Theory Eis BL Nil Alg blk map  4db2ce721b87 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/EisensteinSeriesG2/G2HaarMeasure/PhiEqZeroIff.lean#L164-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/EisensteinSeriesG2/G2HaarMeasure/PhiEqZeroIff.lean#L164-L166

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_EisensteinSeriesG2_G2HaarMeasure_PhiEqZeroIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open GlobalTheory GlobalTheory.EisBL GlobalTheory.EisBL.NilAlg
variable {B : Type} [CommRing B] {n : Type} [Fintype n] [DecidableEq n]

theorem P2M_GlobalTheory_EisBL_NilAlg_blk_map__4db2ce721b87 {B' : Type} [CommRing B'] (f : B →+* B') (X : Matrix n n B) : (blk X).map f = blk (X.map f) := by sorry

alias «GlobalTheory».«EisBL».«NilAlg».«blk_map'» := P2M_GlobalTheory_EisBL_NilAlg_blk_map__4db2ce721b87
