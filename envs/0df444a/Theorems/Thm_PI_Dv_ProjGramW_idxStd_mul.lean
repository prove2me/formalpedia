-- Prove2me | Theorems.Thm_PI_Dv_ProjGramW_idxStd_mul
-- name    : PI.Dv.ProjGramW.idxStd_mul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T04:59:11.508179+00:00
-- url     : https://prove2.me/theorems/740fae56-59b5-4fc1-86e7-8cc82442ad9f
-- title:
--   Proj Gram W: idx Std mul
-- statement:
--   The Proj Gram W construction uses the idx Std mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionGramMatrices/IdxDet.lean#L147-L168
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionGramMatrices/IdxDet.lean#L147-L168

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionGramMatrices_AlgebraMapNeZeroOfNotMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionGramMatrices_IdxDet
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
variable {K : Type} [Field K] [NumberField K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem PI.Dv.ProjGramW.idxStd_mul (hI : IdxCalc) (w : HeightOneSpectrum (𝓞 K)) {d : ℕ} (C1 C2 : Matrix (Fin d) (Fin d) K)
    (h1 : C1.det ≠ 0) (h2 : C2.det ≠ 0) : idxStd w (C1 * C2) = idxStd w C1 + idxStd w C2 := by sorry
