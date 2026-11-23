-- Prove2me | Theorems.Thm_PI_DvRows_lidx_support_finite
-- name    : PI.DvRows.lidx_support_finite
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:23:05.207248+00:00
-- url     : https://prove2.me/theorems/0e2f2ff9-9195-4acd-9812-ba32a468aa0a
-- title:
--   Dv Rows: lidx support finite
-- statement:
--   The Dv Rows construction uses the lidx support finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionRows/AsmBound.lean#L76-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionRows/AsmBound.lean#L76-L94

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

theorem PI.DvRows.lidx_support_finite (A : HLat K) (hG : A.Good) (M : Submodule (𝓞 K) A.V) (hM : M.FG) {j : ℕ}
    (y : Fin j → A.V) (hy : LinearIndependent K y)
    (hsp : Submodule.span K (M : Set A.V) = Submodule.span K (Set.range y)) :
    (Function.support fun w : HeightOneSpectrum (𝓞 K) =>
      Formalism.HermitianLatticesTheory.lidx w.asIdeal (Submodule.span (𝓞 K) (Set.range y)) M).Finite := by sorry
