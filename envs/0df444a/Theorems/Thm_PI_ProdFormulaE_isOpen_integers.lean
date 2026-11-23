-- Prove2me | Theorems.Thm_PI_ProdFormulaE_isOpen_integers
-- name    : PI.ProdFormulaE.isOpen_integers
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:38:37.280421+00:00
-- url     : https://prove2.me/theorems/c55f937a-5e31-43c2-8c1f-610781b9f803
-- title:
--   Prod Formula E: is Open integers
-- statement:
--   The Prod Formula E construction uses the is Open integers property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProductFormulaHaar/NormIndex.lean#L16-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProductFormulaHaar/NormIndex.lean#L16-L17

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

theorem PI.ProdFormulaE.isOpen_integers : IsOpen ((𝒪[K] : Subring K) : Set K) := by sorry
