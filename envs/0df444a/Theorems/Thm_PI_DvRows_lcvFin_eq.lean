-- Prove2me | Theorems.Thm_PI_DvRows_lcvFin_eq
-- name    : PI.DvRows.lcvFin_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:22:41.932909+00:00
-- url     : https://prove2.me/theorems/b9e26a41-0983-4152-ad00-73e8143b3883
-- title:
--   Dv Rows: lcv Fin eq
-- statement:
--   The Dv Rows construction uses the lcv Fin eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionRows/AsmBound.lean#L96-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionRows/AsmBound.lean#L96-L102

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_Pieces
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_AsmBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.DvRows
open NumberField IsDedekindDomain Formalism.BasicNotions PI.Dv Formalism.LFunctionChainParameters.LLcv
variable {K : Type} [Field K] [NumberField K] [StarRing K] [NumberField.IsTotallyComplex K]

theorem PI.DvRows.lcvFin_eq (A : HLat K) {j : ℕ} (y : Fin j → A.V) (M : Submodule (𝓞 K) A.V) :
    lcvFin y M = 2 * ∑ᶠ w : HeightOneSpectrum (𝓞 K),
      lw K w * (Formalism.HermitianLatticesTheory.lidx w.asIdeal (Submodule.span (𝓞 K) (Set.range y)) M : ℝ) := by sorry
