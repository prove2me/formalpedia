-- Prove2me | Theorems.Thm_PI_DvRows_eq_zero_of_orth
-- name    : PI.DvRows.eq_zero_of_orth
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:30:58.630294+00:00
-- url     : https://prove2.me/theorems/6829f0cd-5316-4461-b23f-d798f3ed992a
-- title:
--   Dv Rows: eq zero of orth
-- statement:
--   The Dv Rows construction uses the eq zero of orth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionRows/LatticeFinitelyGenerated.lean#L184-L214
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionRows/LatticeFinitelyGenerated.lean#L184-L214

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_Pieces
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndexDeterminant_NegLogValuation
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_LatticeFinitelyGenerated
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

theorem PI.DvRows.eq_zero_of_orth (A : HLat K) (e : Module.End K A.V) (n : ℕ) (h : A.V →ₗ⋆[K] A.V →ₗ[K] K)
    (hH : IsHermE A e h) (hee : e * e = e) (hn : 0 < n) (S : Set A.V)
    (hS : Submodule.span K S = ⊤) (y : A.V) (hy : y ∈ LinearMap.range e)
    (h0 : ∀ g ∈ S, h (((n : ℕ) : 𝓞 K) • e g) y = 0) : y = 0 := by sorry
