-- Prove2me | Theorems.Thm_PI_ProdFormulaE_modF_mul
-- name    : PI.ProdFormulaE.modF_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:38:20.596831+00:00
-- url     : https://prove2.me/theorems/75f50cef-6bc7-4ede-b883-cc22bec0545f
-- title:
--   Prod Formula E: mod F mul
-- statement:
--   The Prod Formula E construction uses the mod F mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProductFormulaHaar/NormMod.lean#L33-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProductFormulaHaar/NormMod.lean#L33-L41

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_NormMod
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
open PI PI.ProdFormulaE
variable {K : Type} [Field K] [TopologicalSpace K] [IsTopologicalRing K] [LocallyCompactSpace K]

theorem PI.ProdFormulaE.modF_mul (a b : K) : modF K (a * b) = modF K a * modF K b := by sorry
