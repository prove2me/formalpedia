-- Prove2me | Theorems.Thm_PI_DvRows_partA
-- name    : PI.DvRows.partA
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:28:51.247428+00:00
-- url     : https://prove2.me/theorems/75dc5960-dd64-412c-aa1c-441e52de1a4d
-- title:
--   Dv Rows: part A
-- statement:
--   The Dv Rows construction uses the part A property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionRows/ValLeOneOfMemRange.lean#L153-L225
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionRows/ValLeOneOfMemRange.lean#L153-L225

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

theorem PI.DvRows.partA (A : HLat K) (e : Module.End K A.V) (n : ℕ) (h : A.V →ₗ⋆[K] A.V →ₗ[K] K)
    (hP : IsProj A e n) (hH : IsHermE A e h) (hD : ∀ w, DualInAt A h A.L w)
    (U : Submodule K A.V) (hU : U ≤ LinearMap.range e) (w : HeightOneSpectrum (𝓞 K)) (k : ℤ)
    (hk : IsValG A e h U w k) :
    k ≤ ((dimE A e : ℤ) - (Module.finrank K U : ℤ)) * vAdd w ((n : ℕ) : K) := by sorry
