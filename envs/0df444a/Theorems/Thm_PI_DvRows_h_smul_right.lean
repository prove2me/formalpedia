-- Prove2me | Theorems.Thm_PI_DvRows_h_smul_right
-- name    : PI.DvRows.h_smul_right
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:59:17.591794+00:00
-- url     : https://prove2.me/theorems/e22a19a4-950e-4401-9e44-1c3e55109fdf
-- title:
--   Dv Rows: h smul right
-- statement:
--   The Dv Rows construction uses the h smul right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionRows/ValLeOneOfMemRange.lean#L81-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionRows/ValLeOneOfMemRange.lean#L81-L84

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DivisionRowsRationalLattice
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_ValLeOneOfMemRange
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
open NumberField IsDedekindDomain Formalism.BasicNotions PI.Dv
variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem PI.DvRows.h_smul_right {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K) (c : 𝓞 K) (x y : V) :
    h x (c • y) = algebraMap (𝓞 K) K c * h x y := by sorry
