-- Prove2me | Theorems.Thm_PositivityTheory_ThKH_Evl_schr_mem
-- name    : PositivityTheory.ThKH.Evl.schr_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:43:07.251213+00:00
-- url     : https://prove2.me/theorems/30600a9a-e682-4f9a-a529-b46c5ecd74ec
-- title:
--   Evl: schr mem
-- statement:
--   The Evl construction uses the schr mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/LocalThetaKernels/EvlLoc.lean#L29-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/LocalThetaKernels/EvlLoc.lean#L29-L36

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_GoodCharIsLocallyConstant
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_IntegrablePair
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_CyclicAndLine
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_ExistsEqMulApplyZero
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_ExistsInvariantForm
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_DualNumberGraphFiltrationIsotropicOfSkew
import Definitions.Def_Development_WeilBound_CoreStatements_LocalThetaKernels_EvlLoc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix GlobalTheory.WeilM MeasureTheory
open PositivityTheory PositivityTheory.ThKH PositivityTheory.ThKH.Evl
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Invertible (2 : k)]
  {κ : Type} [Fintype κ] {ψ : AddChar k ℂ}

theorem PositivityTheory.ThKH.Evl.schr_mem (hc : Continuous ψ) (w : (κ → k) × (κ → k)) {φ : (κ → k) → ℂ} (hφ : φ ∈ SB (κ → k)) :
    schr ψ w φ ∈ SB (κ → k) := by sorry
