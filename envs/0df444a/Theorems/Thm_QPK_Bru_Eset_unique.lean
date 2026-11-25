-- Prove2me | Theorems.Thm_QPK_Bru_Eset_unique
-- name    : QPK.Bru.Eset_unique
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:54:43.559717+00:00
-- url     : https://prove2.me/theorems/09c18025-46ad-5d85-9da2-8efbf4a75e77
-- title:
--   Bru: Eset unique
-- statement:
--   The Bru construction uses the Eset unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilQuotientHaar/BruhatDecomposition.lean#L78-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilQuotientHaar/BruhatDecomposition.lean#L78-L83

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

theorem QPK.Bru.Eset_unique {μ : Measure G} {K : ℕ → Set G} {x : G} {n m : ℕ}
    (hn : x ∈ Eset μ K n) (hm : x ∈ Eset μ K m) : n = m := by sorry
