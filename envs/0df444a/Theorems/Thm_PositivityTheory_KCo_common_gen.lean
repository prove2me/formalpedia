-- Prove2me | Theorems.Thm_PositivityTheory_KCo_common_gen
-- name    : PositivityTheory.KCo.common_gen
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:51:47.734598+00:00
-- url     : https://prove2.me/theorems/d833c6e9-40e2-572b-9ba2-ccbe1bca0f39
-- title:
--   KCo: common gen
-- statement:
--   The KCo construction uses the common gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/LocallyConstantCoinvariants/LocConstChar.lean#L14-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/LocallyConstantCoinvariants/LocConstChar.lean#L14-L49

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

theorem PositivityTheory.KCo.common_gen (hκ : κ = Fintype.card a) (w w' : SB (RankIn k a a {κ})) :
    ∃ t, w ∈ Submodule.span ℂ (Set.range fun g : GL a k => rightRep (k := k) a a κ g t) ∧
      w' ∈ Submodule.span ℂ (Set.range fun g : GL a k => rightRep (k := k) a a κ g t) := by sorry
