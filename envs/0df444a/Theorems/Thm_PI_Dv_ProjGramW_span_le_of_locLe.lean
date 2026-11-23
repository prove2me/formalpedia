-- Prove2me | Theorems.Thm_PI_Dv_ProjGramW_span_le_of_locLe
-- name    : PI.Dv.ProjGramW.span_le_of_locLe
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:18:22.186083+00:00
-- url     : https://prove2.me/theorems/418cd33e-fae3-4a1e-a5eb-a0ff7eeaa2c8
-- title:
--   Proj Gram W: span le of loc Le
-- statement:
--   The Proj Gram W construction uses the span le of loc Le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionGramMatrices/AlgebraMapNeZeroOfNotMem.lean#L42-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionGramMatrices/AlgebraMapNeZeroOfNotMem.lean#L42-L52

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

theorem PI.Dv.ProjGramW.span_le_of_locLe (w : HeightOneSpectrum (𝓞 K)) {X Y : Submodule (𝓞 K) V} (h : LocLe w 0 X Y) :
    Submodule.span K (X : Set V) ≤ Submodule.span K (Y : Set V) := by sorry
