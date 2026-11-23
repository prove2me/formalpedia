-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_A5x3_sum_over_dual__ff440f43ee65
-- name    : P2M_Formalism_FourierDecayAlt_P_A5x3_sum_over_dual__ff440f43ee65
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:02:39.833808+00:00
-- url     : https://prove2.me/theorems/32d168d3-4c4f-4798-b2a3-a1e37682f81d
-- title:
--   P2 M Formalism Fourier Decay Alt P A5x3 sum over dual  ff440f43ee65: P2 M Formalism Fourier Decay Alt P A5x3 sum over dual  ff440f43ee65
-- statement:
--   The P2 M Formalism Fourier Decay Alt P A5x3 sum over dual  ff440f43ee65 construction uses the P2 M Formalism Fourier Decay Alt P A5x3 sum over dual  ff440f43ee65 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CharacterOrthogonalityDual.lean#L211-L227
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CharacterOrthogonalityDual.lean#L211-L227

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CharacterOrthogonalityDual
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x3
variable {K : Type} [CommRing K] {R : Subring K} {ψ : AddChar K ℂ}
variable {C : Type} [AddCommGroup C] [Module R C]
open Classical

theorem P2M_Formalism_FourierDecayAlt_P_A5x3_sum_over_dual__ff440f43ee65 (h : ∀ a : K, (∀ r ∈ R, ψ (a * r) = 1) ↔ a ∈ R) [Finite C]
    (hsep : ∀ c : C, (∀ α : C →ₗ[R] KR R, α c = 0) → c = 0) (x : C) :
    ∑ᶠ α : C →ₗ[R] KR R, psiKR R ψ (α x) =
      if x = 0 then (Nat.card (C →ₗ[R] KR R) : ℂ) else 0 := by sorry

alias «Formalism».«FourierDecayAlt».«P».«A5x3».«sum_over_dual'» := P2M_Formalism_FourierDecayAlt_P_A5x3_sum_over_dual__ff440f43ee65
