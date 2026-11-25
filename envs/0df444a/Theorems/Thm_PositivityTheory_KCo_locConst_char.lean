-- Prove2me | Theorems.Thm_PositivityTheory_KCo_locConst_char
-- name    : PositivityTheory.KCo.locConst_char
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T08:51:20.657501+00:00
-- url     : https://prove2.me/theorems/220f80f3-98af-588e-bd40-74e6a45c27a7
-- title:
--   KCo: loc Const char
-- statement:
--   The KCo construction uses the loc Const char property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/LocallyConstantCoinvariants/LocConstChar.lean#L62-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/LocallyConstantCoinvariants/LocConstChar.lean#L62-L69

import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FiniteTwistedRankQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_WeilBound_CoreStatements_LocallyConstantCoinvariants_LocConstChar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.KCo
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences GlobalTheory.RankStrataProof GlobalTheory.CompanionTheory.ThetaGLLen GlobalTheory.CompanionTheory.ThetaGLLen.FullRank Matrix Topology
  MeasureTheory
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {a : Type} [Fintype a] [DecidableEq a] {κ : ℕ}

theorem PositivityTheory.KCo.locConst_char {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {χ : G →* ℂˣ} (h : IsSmoothChar χ) :
    IsLocallyConstant fun g => (χ g : ℂ) := by sorry
