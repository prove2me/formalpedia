-- Prove2me | Theorems.Thm_PositivityTheory_KCo_exists_fun
-- name    : PositivityTheory.KCo.exists_fun
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T08:52:35.599689+00:00
-- url     : https://prove2.me/theorems/3d797288-1560-5d12-a1e0-6de536a3c54d
-- title:
--   KCo: exists fun
-- statement:
--   The KCo construction uses the exists fun property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/LocallyConstantCoinvariants/LocConstChar.lean#L71-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/LocallyConstantCoinvariants/LocConstChar.lean#L71-L138

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

theorem PositivityTheory.KCo.exists_fun (hκ : κ = Fintype.card a) {ξ : GL a k →* ℂˣ} (hξ : IsSmoothChar ξ) :
    ∃ l : SB (RankIn k a a {κ}) →ₗ[ℂ] ℂ, Function.Surjective l ∧
      (∀ (g p : GL a k) φ, l (fibBase a a κ (g, p) φ) = (ξ p : ℂ) * ((ξ g)⁻¹ : ℂˣ) * l φ) ∧
      ∀ φ, l φ = 0 → φ ∈ twRel (rightRep (k := k) a a κ) ξ⁻¹ := by sorry
