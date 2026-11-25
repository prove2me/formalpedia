-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_exists_polyDiff_basis_5ea53f5caf5a
-- name    : P2M_GroundTheory_Heights__Heights_exists_polyDiff_basis_5ea53f5caf5a
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:49:11.183845+00:00
-- url     : https://prove2.me/theorems/9c47d919-6062-56e4-9e04-b21e39787d80
-- title:
--   P2 M Ground Theory Heights  Heights exists poly Diff basis 5ea53f5caf5a: P2 M Ground Theory Heights  Heights exists poly Diff basis 5ea53f5caf5a
-- statement:
--   The P2 M Ground Theory Heights  Heights exists poly Diff basis 5ea53f5caf5a construction uses the P2 M Ground Theory Heights  Heights exists poly Diff basis 5ea53f5caf5a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PPolyLocalGeneratorsDiff.lean#L141-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PPolyLocalGeneratorsDiff.lean#L141-L182

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsPolyLocalGenerators
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PPolyLocalGeneratorsDiff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial Module
noncomputable section
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_exists_polyDiff_basis_5ea53f5caf5a (J : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin n → ℂ) :
    ∃ q : Fin (n - finrank ℂ (polyTangent (J : Set (MvPolynomial (Fin n) ℂ)) p)) →
        MvPolynomial (Fin n) ℂ,
      (∀ i, q i ∈ J) ∧ LinearIndependent ℂ (polyDiff p ∘ q) ∧
        ∀ f ∈ J, polyDiff p f ∈ Submodule.span ℂ (Set.range (polyDiff p ∘ q)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«exists_polyDiff_basis» := P2M_GroundTheory_Heights__Heights_exists_polyDiff_basis_5ea53f5caf5a
