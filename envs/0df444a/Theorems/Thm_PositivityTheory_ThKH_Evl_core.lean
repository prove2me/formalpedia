-- Prove2me | Theorems.Thm_PositivityTheory_ThKH_Evl_core
-- name    : PositivityTheory.ThKH.Evl.core
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:05:42.641801+00:00
-- url     : https://prove2.me/theorems/b9990261-f3e3-4f86-9dd7-81fff76b8f3e
-- title:
--   Evl: core
-- statement:
--   The Evl construction uses the core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/LocalThetaKernels/EvlLoc.lean#L67-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/LocalThetaKernels/EvlLoc.lean#L67-L93

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

theorem PositivityTheory.ThKH.Evl.core (hc : Continuous ψ) (hn : ∀ x, ‖ψ x‖ = 1) (h1 : ψ ≠ 1) {φ₀ : (κ → k) → ℂ} (h₀ : φ₀ ∈ SB (κ → k)) (hne : φ₀ ≠ 0)
    (A : Set ((κ → k) × (κ → k))) (l : ((κ → k) → ℂ) →ₗ[ℂ] ℂ) (hA : ∀ a ∈ A, ∀ φ ∈ SB (κ → k), l (schr ψ a φ) = l φ)
    (hs : ∀ w, ∃ a ∈ A, ∃ b, w = a + b ∧ ((∃ c : ℂ, schr ψ b φ₀ = c • φ₀) ∨
      ∃ a' ∈ A, schr ψ a' φ₀ = φ₀ ∧ ψ (a'.1 ⬝ᵥ b.2 - b.1 ⬝ᵥ a'.2) ≠ 1))
    (hl : l φ₀ = 0) : ∀ φ ∈ SB (κ → k), l φ = 0 := by sorry
