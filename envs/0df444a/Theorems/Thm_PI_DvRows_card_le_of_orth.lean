-- Prove2me | Theorems.Thm_PI_DvRows_card_le_of_orth
-- name    : PI.DvRows.card_le_of_orth
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:59:18.602579+00:00
-- url     : https://prove2.me/theorems/ba261104-2b79-471e-8ede-0167df8dee36
-- title:
--   Dv Rows: card le of orth
-- statement:
--   The Dv Rows construction uses the card le of orth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionRows/ValLeOneOfMemRange.lean#L86-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionRows/ValLeOneOfMemRange.lean#L86-L151

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

theorem PI.DvRows.card_le_of_orth (A : HLat K) (e : Module.End K A.V) (h : A.V →ₗ⋆[K] A.V →ₗ[K] K)
    (hee : e * e = e) (hH : IsHermE A e h) (U : Submodule K A.V) (hU : U ≤ LinearMap.range e)
    {d : ℕ} (y : Fin d → A.V) (hy : LinearIndependent K y) (hye : ∀ i, y i ∈ LinearMap.range e)
    (hyU : ∀ i, ∀ u ∈ U, h (y i) u = 0) :
    d + Module.finrank K U ≤ dimE A e := by sorry
