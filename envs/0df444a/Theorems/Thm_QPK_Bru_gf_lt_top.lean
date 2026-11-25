-- Prove2me | Theorems.Thm_QPK_Bru_gf_lt_top
-- name    : QPK.Bru.gf_lt_top
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:51:09.296385+00:00
-- url     : https://prove2.me/theorems/39095ff7-e13b-4508-9408-4879a7348282
-- title:
--   Bru: gf lt top
-- statement:
--   The Bru construction uses the gf lt top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilQuotientHaar/BruhatDecomposition.lean#L40-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilQuotientHaar/BruhatDecomposition.lean#L40-L44

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilQuotientHaar_HaarExist
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilQuotientHaar_BruhatDecomposition
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal
open QPK
open QPK.Bru
variable {G : Type} [TopologicalSpace G] [Group G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

theorem QPK.Bru.gf_lt_top (μ : Measure G) [IsFiniteMeasureOnCompacts μ] (K : ℕ → Set G)
    (hK : ∀ n, IsCompact (K n)) (n : ℕ) (x : G) : gf μ K n x < ⊤ := by sorry
