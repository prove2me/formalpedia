-- Prove2me | Theorems.Thm_PI_ProdFormulaE_isCompact_integers
-- name    : PI.ProdFormulaE.isCompact_integers
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:17:27.066002+00:00
-- url     : https://prove2.me/theorems/dd2b5c6c-b527-5423-b2d7-845c3931fa13
-- title:
--   Prod Formula E: is Compact integers
-- statement:
--   The Prod Formula E construction uses the is Compact integers property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProductFormulaHaar/NormIndex.lean#L19-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProductFormulaHaar/NormIndex.lean#L19-L20

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_NormMod
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_NormIndex
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory ValuativeRel
open scoped Pointwise ENNReal NNReal
open PI PI.ProdFormulaE
variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [MeasurableSpace K] [BorelSpace K]

theorem PI.ProdFormulaE.isCompact_integers : IsCompact ((𝒪[K] : Subring K) : Set K) := by sorry
