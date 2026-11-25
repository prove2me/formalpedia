-- Prove2me | Theorems.Thm_PI_DvRows_absNorm_conj
-- name    : PI.DvRows.absNorm_conj
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:29:15.618999+00:00
-- url     : https://prove2.me/theorems/60300bca-36f2-4be7-a97d-a9f3f1a7e0f7
-- title:
--   Dv Rows: abs Norm conj
-- statement:
--   The Dv Rows construction uses the abs Norm conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionRows/LatticeFinitelyGenerated.lean#L90-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionRows/LatticeFinitelyGenerated.lean#L90-L94

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

theorem PI.DvRows.absNorm_conj (w : HeightOneSpectrum (𝓞 K)) :
    Ideal.absNorm (conjW w).asIdeal = Ideal.absNorm w.asIdeal := by sorry
