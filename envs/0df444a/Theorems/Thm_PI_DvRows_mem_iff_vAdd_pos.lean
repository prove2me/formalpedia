-- Prove2me | Theorems.Thm_PI_DvRows_mem_iff_vAdd_pos
-- name    : PI.DvRows.mem_iff_vAdd_pos
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:22:28.780827+00:00
-- url     : https://prove2.me/theorems/50798f27-f31a-42d3-90c3-4c501aaa3d07
-- title:
--   Dv Rows: mem iff v Add pos
-- statement:
--   The Dv Rows construction uses the mem iff v Add pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionRows/LatticeFinitelyGenerated.lean#L406-L411
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionRows/LatticeFinitelyGenerated.lean#L406-L411

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
open Formalism.HermitianLatticesTheory
variable {K : Type} [Field K] [NumberField K]

theorem PI.DvRows.mem_iff_vAdd_pos (w : HeightOneSpectrum (𝓞 K)) {r : 𝓞 K} (hr : r ≠ 0) :
    r ∈ w.asIdeal ↔ 0 < vAdd w (algebraMap (𝓞 K) K r) := by sorry
