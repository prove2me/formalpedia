-- Prove2me | Theorems.Thm_PI_Dv_ProjGramW_vAdd_algebraMap_nonneg
-- name    : PI.Dv.ProjGramW.vAdd_algebraMap_nonneg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:18:33.917121+00:00
-- url     : https://prove2.me/theorems/132ab380-13c8-44a6-875e-9f52338a3585
-- title:
--   Proj Gram W: v Add algebra Map nonneg
-- statement:
--   The Proj Gram W construction uses the v Add algebra Map nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionGramMatrices/AlgebraMapNeZeroOfNotMem.lean#L75-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionGramMatrices/AlgebraMapNeZeroOfNotMem.lean#L75-L86

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DivisionRowsRationalLattice
import Definitions.Def_Formalism_PeriodIntegrals_IdxCalc
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionGramMatrices_AlgebraMapNeZeroOfNotMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.ProjGramW
open NumberField IsDedekindDomain Formalism.BasicNotions
variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem PI.Dv.ProjGramW.vAdd_algebraMap_nonneg (w : HeightOneSpectrum (𝓞 K)) (r : 𝓞 K) :
    0 ≤ vAdd w (algebraMap (𝓞 K) K r) := by sorry
