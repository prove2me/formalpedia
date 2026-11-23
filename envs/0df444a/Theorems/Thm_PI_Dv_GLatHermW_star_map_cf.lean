-- Prove2me | Theorems.Thm_PI_Dv_GLatHermW_star_map_cf
-- name    : PI.Dv.GLatHermW.star_map_cf
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:16:44.315368+00:00
-- url     : https://prove2.me/theorems/d8c42db3-9744-4e49-8f1d-dcf0cfd4bfb6
-- title:
--   GLat Herm W: star map cf
-- statement:
--   The GLat Herm W construction uses the star map cf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianGroupLattices/AsAlgebraHomEG.lean#L29-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianGroupLattices/AsAlgebraHomEG.lean#L29-L36

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SameFormAllLevels
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianGroupLattices_StarMapTraceOfPowEqOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianGroupLattices_AsAlgebraHomEG
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.GLatHermW
open PI.Dv
variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G]

theorem PI.Dv.GLatHermW.star_map_cf (σ : K →+* ℂ) (T : GoodSet K G) (g : G) :
    star (σ (cf T g)) = σ (cf T g⁻¹) := by sorry
