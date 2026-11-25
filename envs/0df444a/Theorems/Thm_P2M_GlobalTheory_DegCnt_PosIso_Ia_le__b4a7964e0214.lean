-- Prove2me | Theorems.Thm_P2M_GlobalTheory_DegCnt_PosIso_Ia_le__b4a7964e0214
-- name    : P2M_GlobalTheory_DegCnt_PosIso_Ia_le__b4a7964e0214
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T06:37:30.586039+00:00
-- url     : https://prove2.me/theorems/b173bd34-05e2-48cc-9de5-89958f03a430
-- title:
--   P2 M Global Theory Deg Cnt Pos Iso Ia le  b4a7964e0214: P2 M Global Theory Deg Cnt Pos Iso Ia le  b4a7964e0214
-- statement:
--   The P2 M Global Theory Deg Cnt Pos Iso Ia le  b4a7964e0214 construction uses the P2 M Global Theory Deg Cnt Pos Iso Ia le  b4a7964e0214 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/NormalFormIdealDivisibility.lean#L302-L307
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/NormalFormIdealDivisibility.lean#L302-L307

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SameBlockAppend
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NormalFormIdealDivisibility
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Formalism.HermitianLatticeCounting.P Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical nonZeroDivisors
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.PosIso
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {H : HermSpace K V} {r : ℕ}
omit [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem P2M_GlobalTheory_DegCnt_PosIso_Ia_le__b4a7964e0214 (N : NF H r) (n : ℕ) : Ia N n ≤ N.F'.Xa n := by sorry

alias «GlobalTheory».«DegCnt».«PosIso».«Ia_le'» := P2M_GlobalTheory_DegCnt_PosIso_Ia_le__b4a7964e0214
