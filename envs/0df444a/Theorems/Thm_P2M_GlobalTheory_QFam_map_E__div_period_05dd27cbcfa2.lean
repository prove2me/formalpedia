-- Prove2me | Theorems.Thm_P2M_GlobalTheory_QFam_map_E__div_period_05dd27cbcfa2
-- name    : P2M_GlobalTheory_QFam_map_E__div_period_05dd27cbcfa2
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T00:09:09.24227+00:00
-- url     : https://prove2.me/theorems/167f62fc-09e5-44d5-ba1d-d9b47c5944de
-- title:
--   P2 M Global Theory QFam map E  div period 05dd27cbcfa2: P2 M Global Theory QFam map E  div period 05dd27cbcfa2
-- statement:
--   The P2 M Global Theory QFam map E  div period 05dd27cbcfa2 construction uses the P2 M Global Theory QFam map E  div period 05dd27cbcfa2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MapEisensteinDivPeriod.lean#L31-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MapEisensteinDivPeriod.lean#L31-L36

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModGEis
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModQPrin
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModJTau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MapEisensteinDivPeriod
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)
open GlobalTheory GlobalTheory.QFam

theorem P2M_GlobalTheory_QFam_map_E__div_period_05dd27cbcfa2 (g : ℂ ≃+* ℂ) {Λ₀ Λ₁ : PeriodPair} {c₀ c₁ Ω₀ Ω₁ : ℂ} {τ₀ τ₁ : ℍ}
    (h₀ : IsTauOf Λ₀ c₀ τ₀) (h₁ : IsTauOf Λ₁ c₁ τ₁)
    (h : g (Λ₀.g₂ / Ω₀ ^ 4) = Λ₁.g₂ / Ω₁ ^ 4) :
    g (E₄ τ₀ / (Ω₀ * c₀ / (2 * Real.pi * Complex.I)) ^ 4)
      = E₄ τ₁ / (Ω₁ * c₁ / (2 * Real.pi * Complex.I)) ^ 4 := by sorry

alias «GlobalTheory».«QFam».«map_E₄_div_period» := P2M_GlobalTheory_QFam_map_E__div_period_05dd27cbcfa2
