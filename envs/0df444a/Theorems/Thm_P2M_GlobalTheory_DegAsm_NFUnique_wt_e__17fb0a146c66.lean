-- Prove2me | Theorems.Thm_P2M_GlobalTheory_DegAsm_NFUnique_wt_e__17fb0a146c66
-- name    : P2M_GlobalTheory_DegAsm_NFUnique_wt_e__17fb0a146c66
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T08:01:26.717468+00:00
-- url     : https://prove2.me/theorems/62e6dac2-a5a1-59e4-bb85-5b25da1134f9
-- title:
--   P2 M Global Theory Deg Asm NFUnique wt e  17fb0a146c66: P2 M Global Theory Deg Asm NFUnique wt e  17fb0a146c66
-- statement:
--   The P2 M Global Theory Deg Asm NFUnique wt e  17fb0a146c66 construction uses the P2 M Global Theory Deg Asm NFUnique wt e  17fb0a146c66 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermFramePairNormalFormUniqueUpToUnipotent.lean#L94-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermFramePairNormalFormUniqueUpToUnipotent.lean#L94-L95

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_AdaptSelf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairNormalFormGeometrySummary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FlagFramesSameGradedDefinitePartLatticeEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairNormalFormUniqueUpToUnipotent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt GlobalTheory.DegAsm
open scoped Pointwise ENNReal Classical
open Formalism.HermitianLatticeCounting.P
open GlobalTheory GlobalTheory.DegAsm GlobalTheory.DegAsm.NFUnique
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {H : HermSpace K V} {r : ℕ}
variable [NumberField K]

theorem P2M_GlobalTheory_DegAsm_NFUnique_wt_e__17fb0a146c66 (N : NF H r) {w : V} (hw : w ∈ N.Wt) (a : Fin (r + 1)) : H.B (N.F'.e a) w = 0 := by sorry

alias «GlobalTheory».«DegAsm».«NFUnique».«wt_e'» := P2M_GlobalTheory_DegAsm_NFUnique_wt_e__17fb0a146c66
