-- Prove2me | Theorems.Thm_PI_SerBridgeGLW_isConstituent_hc_iff
-- name    : PI.SerBridgeGLW.isConstituent_hc_iff
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:37:14.154233+00:00
-- url     : https://prove2.me/theorems/ada06e53-b19e-5c12-97be-daeaf6f79d53
-- title:
--   Ser Bridge GLW: is Constituent hc iff
-- statement:
--   The Ser Bridge GLW construction uses the is Constituent hc iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IrreducibleCharacterSeries/FrobeniusSumFormula.lean#L52-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IrreducibleCharacterSeries/FrobeniusSumFormula.lean#L52-L115

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IrreducibleCharacterSeries_IrrCharIff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IrreducibleCharacterSeries_ConjugateCharacterFormula
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IrreducibleCharacterSeries_FrobeniusSumFormula
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Formalism.IrreducibleCountingLemmas.TYPES
open PI PI.SerBridgeGLW

theorem PI.SerBridgeGLW.isConstituent_hc_iff (K : Type) [Field K] [Fintype K] [DecidableEq K] {ι : Type} [Fintype ι]
    [DecidableEq ι] {s : ℕ} (b : ι → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K))
    (V : FDRep ℂ (GL ι K)) :
    IsConstituent V (hcRep K b lam) ↔
      ∃ ψ : V →ₗ[ℂ] PiTensorProduct ℂ (fun c => (lam c : Type)), ψ ≠ 0 ∧
        ∀ p : parab K b, ψ ∘ₗ V.ρ p.1 = infl K b lam p ∘ₗ ψ := by sorry
