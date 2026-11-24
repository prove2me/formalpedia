-- Prove2me | Theorems.Thm_PositivityTheory_ThKF0_Chr_Fr_embeddingAtLocalFactor
-- name    : PositivityTheory.ThKF0.Chr.Fr.embeddingAtLocalFactor
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:43:39.885556+00:00
-- url     : https://prove2.me/theorems/b521da48-a27a-42f0-b823-ad35bf0bf5f3
-- title:
--   Fr: embedding At Local Factor
-- statement:
--   The Fr construction uses the embedding At Local Factor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LeviDeterminants/CharacterAdmissibility/DoublingGramFromBlocks.lean#L86-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LeviDeterminants/CharacterAdmissibility/DoublingGramFromBlocks.lean#L86-L89

import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_SiegelTransportAlg
import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_CharacterAdmissibility_DoublingGramFromBlocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKF0 PositivityTheory.ThKF0.Chr
open Matrix GlobalTheory.WeilM PositivityTheory.ThK.SiegelT
variable {R : Type} [CommRing R] {E : Type} [CommRing E] [Algebra R E] {c : E →ₐ[R] E}
  {β β₁ μ ν : Type} [Fintype β] [DecidableEq β] [Fintype β₁] [DecidableEq β₁] [Fintype μ] [DecidableEq μ]
  [Fintype ν] [DecidableEq ν]
variable {J : Matrix β β E} {J₁ : Matrix β₁ β₁ E} {H : Matrix μ μ E} {ι : Matrix β β₁ E} {Z : Matrix β μ E}
  {π : Matrix β₁ β E} {ρ : Matrix μ β E}

theorem PositivityTheory.ThKF0.Chr.Fr.embeddingAtLocalFactor (h : Fr c J J₁ H ι Z π ρ) (p : UG c J₁ × UG c H) : (h.emb p).1.1 * Z = Z * p.2.1.1 := by sorry
