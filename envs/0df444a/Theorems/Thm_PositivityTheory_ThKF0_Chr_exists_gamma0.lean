-- Prove2me | Theorems.Thm_PositivityTheory_ThKF0_Chr_exists_gamma0
-- name    : PositivityTheory.ThKF0.Chr.exists_gamma0
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T09:05:49.152118+00:00
-- url     : https://prove2.me/theorems/3159b19a-2a65-5e46-afac-693783fb1cc8
-- title:
--   Chr: exists gamma0
-- statement:
--   The Chr construction uses the exists gamma0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LeviDeterminants/CharacterAdmissibility/DoublingGramFromBlocks.lean#L104-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LeviDeterminants/CharacterAdmissibility/DoublingGramFromBlocks.lean#L104-L127

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

theorem PositivityTheory.ThKF0.Chr.exists_gamma0 (η : ℤˣ) : ∃ γ : UG c (dbl (hyp ν η : Matrix _ _ E)), γ.1.1 * (diagCols (ν ⊕ ν) : Matrix _ _ E) =
    dd2 (fromRows (1 : Matrix ν ν E) (0 : Matrix ν ν E)) * (fromBlocks 1 0 0 (((η : ℤ) : E) • 1) : Matrix (ν ⊕ ν) (ν ⊕ ν) E) := by sorry
