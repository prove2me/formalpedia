-- Prove2me | Theorems.Thm_P2M_GlobalTheory_SerConj_bcEquiv___3b5f4a7a85e0
-- name    : P2M_GlobalTheory_SerConj_bcEquiv___3b5f4a7a85e0
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:10:25.137809+00:00
-- url     : https://prove2.me/theorems/c8440df2-6d47-4216-b781-1d29d21de17c
-- title:
--   P2 M Global Theory Ser Conj bc Equiv   3b5f4a7a85e0: P2 M Global Theory Ser Conj bc Equiv   3b5f4a7a85e0
-- statement:
--   The P2 M Global Theory Ser Conj bc Equiv   3b5f4a7a85e0 construction uses the P2 M Global Theory Ser Conj bc Equiv   3b5f4a7a85e0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/StarCoeffEisensteinSeriesReversePoly.lean#L90-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/StarCoeffEisensteinSeriesReversePoly.lean#L90-L97

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_CoeffZeroNeOfMonicIrr
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IrreducibleCharacterSeries_ConjugateCharacterFormula
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RootsReverseProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_StarCoeffEisensteinSeriesReversePoly
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial CategoryTheory
open GlobalTheory GlobalTheory.SerConj
open Formalism.IrreducibleCountingLemmas.TYPES
variable {Γ : Type} [Group Γ]

theorem P2M_GlobalTheory_SerConj_bcEquiv___3b5f4a7a85e0 (σ : ℂ ≃+* ℂ) (τ : FDRep ℂ Γ) (γ : Γ) (v : τ) :
    bcEquiv σ τ (τ.ρ γ v) = (bc σ τ).ρ γ (bcEquiv σ τ v) := by sorry

alias «GlobalTheory».«SerConj».«bcEquiv_ρ» := P2M_GlobalTheory_SerConj_bcEquiv___3b5f4a7a85e0
