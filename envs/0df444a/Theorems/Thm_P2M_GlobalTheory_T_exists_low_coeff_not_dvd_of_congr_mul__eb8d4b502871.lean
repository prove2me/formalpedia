-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_exists_low_coeff_not_dvd_of_congr_mul__eb8d4b502871
-- name    : P2M_GlobalTheory_T_exists_low_coeff_not_dvd_of_congr_mul__eb8d4b502871
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T00:10:09.421518+00:00
-- url     : https://prove2.me/theorems/d79d7933-4491-465c-85e6-c6825bd7c9ae
-- title:
--   P2 M Global Theory T exists low coeff not dvd of congr mul  eb8d4b502871: P2 M Global Theory T exists low coeff not dvd of congr mul  eb8d4b502871
-- statement:
--   The P2 M Global Theory T exists low coeff not dvd of congr mul  eb8d4b502871 construction uses the P2 M Global Theory T exists low coeff not dvd of congr mul  eb8d4b502871 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsLowCoeffNotDvdOfCongrMulStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsLowCoeffNotDvdOfCongrMulStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsLowCoeffNotDvdOfCongrMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsLowCoeffNotDvdOfCongrMulStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
set_option maxHeartbeats 1000000

theorem P2M_GlobalTheory_T_exists_low_coeff_not_dvd_of_congr_mul__eb8d4b502871 : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ → ∀ (D g f : PowerSeries O) (m₀ v nT MT : ℕ), (∃ m ≤ m₀, IsUnit (PowerSeries.coeff m D)) → ¬ ϖ ^ (v + 1) ∣ PowerSeries.coeff 0 g → v + 1 ≤ nT → (v + 1) * m₀ ≤ MT → (∀ i ≤ MT, ϖ ^ nT ∣ PowerSeries.coeff i (f - D * g)) → ∃ i ≤ (v + 1) * m₀, ¬ ϖ ^ (v + 1) ∣ PowerSeries.coeff i f := by sorry

alias «GlobalTheory».«T».«exists_low_coeff_not_dvd_of_congr_mul'» := P2M_GlobalTheory_T_exists_low_coeff_not_dvd_of_congr_mul__eb8d4b502871
