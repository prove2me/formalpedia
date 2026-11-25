-- Prove2me | Theorems.Thm_PI_DvRows_mem_comap_pow
-- name    : PI.DvRows.mem_comap_pow
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:29:20.376978+00:00
-- url     : https://prove2.me/theorems/2e01f891-6e04-4baf-8c7c-07e92bd0d92f
-- title:
--   Dv Rows: mem comap pow
-- statement:
--   The Dv Rows construction uses the mem comap pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionRows/LatticeFinitelyGenerated.lean#L24-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionRows/LatticeFinitelyGenerated.lean#L24-L28

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

theorem PI.DvRows.mem_comap_pow (I : Ideal (𝓞 K)) (n : ℕ) (a : 𝓞 K) :
    a ∈ (I.comap (starO K)) ^ n ↔ starO K a ∈ I ^ n := by sorry
